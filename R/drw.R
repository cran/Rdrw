# ====================================================================
# 1. OPTIMIZED MULTIVARIATE KALMAN LOG-LIKELIHOOD
# ====================================================================
drw_log_lik <- function(data, theta) {
  beta <- theta[[1]] # matrix with k rows and (poly.order + 1) columns
  k <- nrow(beta)
  sigma2 <- theta[[2]]
  tau <- theta[[3]]
  
  rho <- matrix(1, nrow = k, ncol = k)  
  rho[upper.tri(rho)] <- theta[[4]]
  rho[lower.tri(rho)] <- t(rho)[lower.tri(rho)]

  det_rho <- det(rho)
  if (is.na(det_rho) || det_rho <= 0) return(-Inf)

  data <- as.matrix(data)

  raw.time <- data[, 1]
  time.range <- max(raw.time) - min(raw.time)
  if (!is.finite(time.range) || time.range <= 0) {
    stop("The observation times must contain at least two distinct finite values.")
  }
  time.comb <- (raw.time - min(raw.time)) / time.range
  leng.time <- length(time.comb)
  
  # Dynamic construction of polynomial design matrix B
  p_order <- ncol(beta) - 1  
  B <- matrix(1, nrow = leng.time, ncol = p_order + 1)
  if (p_order > 0) {
    for (p in 1:p_order) {
      B[, p + 1] <- time.comb^p
    }
  }
  mean.mat <- B %*% t(beta)

  lc.comb <- data[, seq(2, 2 * k, by = 2), drop = FALSE]
  var.lc.comb <- data[, seq(3, 2 * k + 1, by = 2), drop = FALSE]^2
  
  Sigma <- vector("list", leng.time)
  Sigma.star <- vector("list", leng.time)
  
  inv_tau <- 1 / tau
  temp <- outer(inv_tau, inv_tau, "+")
  
  Sigma[[1]] <- (t(rho * sqrt(sigma2)) * sqrt(sigma2)) / temp 

  mu.i <- matrix(0, leng.time, k)
  mu.star.i <- matrix(0, leng.time, k)
  mu.i[1, ] <- mean.mat[1, ]

  delta.t <- diff(time.comb)
  a.i <- exp(-delta.t %*% t(inv_tau)) 
  
  loglik <- 0

  for (t in 1:leng.time) {
    if (t > 1) {
      Sigma[[t]] <- t(a.i[t - 1, ] * Sigma.star[[t - 1]]) * a.i[t - 1, ] + 
                    Sigma[[1]] * (1 - exp(-temp * delta.t[t - 1]))
                    
      m.prev <- mean.mat[t - 1, ]
      m.curr <- mean.mat[t, ]
      mu.i[t, ] <- m.curr + a.i[t - 1, ] * (mu.star.i[t - 1, ] - m.prev)
    }

    lc_row <- lc.comb[t, ]
    q <- which(!is.na(lc_row))
    len_q <- length(q)
    
    if (len_q == 0) {
      Sigma.star[[t]] <- Sigma[[t]]
      mu.star.i[t, ] <- mu.i[t, ]
      next
    }
    
    lc.t <- lc_row[q]
    var.t <- var.lc.comb[t, q]
    
    if (len_q > 1) {
      Qt <- Sigma[[t]][q, q, drop = FALSE] + diag(var.t, nrow = len_q)
      Qt <- (Qt + t(Qt)) / 2 
      
      chol_Qt <- tryCatch(chol(Qt), error = function(e) NULL)
      if (is.null(chol_Qt)) return(-Inf)
      
      invQt <- chol2inv(chol_Qt)
      
      Sigma.star[[t]] <- Sigma[[t]] - Sigma[[t]][, q, drop = FALSE] %*% invQt %*% Sigma[[t]][q, , drop = FALSE]
      diff_mu <- lc.t - mu.i[t, q]
      mu.star.i[t, ] <- mu.i[t, ] + as.numeric(Sigma[[t]][, q, drop = FALSE] %*% invQt %*% diff_mu)
      
      log_det_Qt <- 2 * sum(log(diag(chol_Qt)))
      quad_form <- sum(diff_mu * as.numeric(invQt %*% diff_mu))
      loglik <- loglik - 0.5 * (len_q * log(2 * pi) + log_det_Qt + quad_form)
      
    } else {
      Qt <- Sigma[[t]][q, q] + var.t
      if (Qt <= 0 || is.na(Qt)) return(-Inf)
      invQt <- 1 / Qt
      
      Sigma.star[[t]] <- Sigma[[t]] - (Sigma[[t]][, q, drop = FALSE] %*% Sigma[[t]][q, , drop = FALSE]) * invQt 
      diff_mu <- lc.t - mu.i[t, q]
      mu.star.i[t, ] <- mu.i[t, ] + Sigma[[t]][, q] * diff_mu * invQt
      
      loglik <- loglik - 0.5 * (log(2 * pi) + log(Qt) + (diff_mu^2) * invQt)
    }
  }  
  return(as.numeric(loglik))
}

# ====================================================================
# 2. STREAMLINED BAYESIAN SAMPLER (BLOCK-DIAGONAL PROFILE GIBBS BETA)
# ====================================================================
bayes <- function(data, theta, n.warm, n.sample, k, n_b_per_k,
                  lower_bounds, upper_bounds) {
  
  n.total <- n.warm + n.sample
  n.rho <- k * (k - 1) / 2
  n_beta <- k * n_b_per_k
  
  beta_chain   <- matrix(0, nrow = n.sample, ncol = n_beta)
  sigma2_chain <- matrix(0, nrow = n.sample, ncol = k)
  tau_chain    <- matrix(0, nrow = n.sample, ncol = k)
  rho_chain    <- matrix(0, nrow = n.sample, ncol = n.rho)
  
  sigma2.accept <- matrix(0, nrow = n.total, ncol = k)
  tau.accept    <- matrix(0, nrow = n.total, ncol = k)
  rho.accept    <- matrix(0, nrow = n.total, ncol = n.rho)
  
  curr_beta   <- matrix(theta$beta, nrow = k, byrow = TRUE)
  curr_sigma2 <- theta$sigma2
  curr_tau    <- theta$tau
  curr_rho    <- theta$rho
  
  curr_th_sigma2 <- log(curr_sigma2)
  curr_th_tau    <- log(curr_tau)
  curr_th_rho    <- log((curr_rho + 1) / (1 - curr_rho))
  
  b_sig_low <- lower_bounds[(n_beta + 1) : (n_beta + k)]
  b_sig_upp <- upper_bounds[(n_beta + 1) : (n_beta + k)]
  b_tau_low <- lower_bounds[(n_beta + k + 1) : (n_beta + 2 * k)]
  b_tau_upp <- upper_bounds[(n_beta + k + 1) : (n_beta + 2 * k)]
  if (n.rho > 0) {
    b_rho_low <- lower_bounds[(n_beta + 2 * k + 1) : (n_beta + 2 * k + n.rho)]
    b_rho_upp <- upper_bounds[(n_beta + 2 * k + 1) : (n_beta + 2 * k + n.rho)]
  } else {
    b_rho_low <- numeric(0)
    b_rho_upp <- numeric(0)
  }
  
  log.sigma2.prop.scale <- rep(0.05, k)
  log.tau.prop.scale    <- rep(0.1, k)
  rho.prop.scale        <- rep(0.05, n.rho)
  
  prior_prec_beta <- diag(1e-6, n_beta)
  
  message("Running Bayesian MCMC Posterior Sampling...")
  
  for (iter in 1:n.total) {
    
    # --- STEP 1: GAUSSIAN APPROXIMATION FOR BETA AROUND THE CURRENT VALUE ---
    eps <- 1e-5
    beta_base <- curr_beta
    beta_base_vec <- as.vector(t(beta_base))
    L_0 <- drw_log_lik(data, list(beta_base, curr_sigma2, curr_tau, curr_rho))
    
    grad_b <- rep(0, n_beta)
    Hess_b <- matrix(0, nrow = n_beta, ncol = n_beta)
    
    L_fwd <- rep(0, n_beta)
    L_bwd <- rep(0, n_beta)
    
    for (i in 1:n_beta) {
      beta_fwd_vec <- beta_base_vec
      beta_fwd_vec[i] <- beta_fwd_vec[i] + eps
      beta_fwd <- matrix(beta_fwd_vec, nrow = k, byrow = TRUE)
      L_fwd[i] <- drw_log_lik(data, list(beta_fwd, curr_sigma2, curr_tau, curr_rho))
      
      beta_bwd_vec <- beta_base_vec
      beta_bwd_vec[i] <- beta_bwd_vec[i] - eps
      beta_bwd <- matrix(beta_bwd_vec, nrow = k, byrow = TRUE)
      L_bwd[i] <- drw_log_lik(data, list(beta_bwd, curr_sigma2, curr_tau, curr_rho))
      
      grad_b[i] <- (L_fwd[i] - L_bwd[i]) / (2 * eps)
      Hess_b[i, i] <- (L_fwd[i] + L_bwd[i] - 2 * L_0) / (eps^2)
    }
    
    for (g in 1:k) {
      idx <- ((g - 1) * n_b_per_k + 1) : (g * n_b_per_k)
      if (length(idx) > 1) {
        for (i in 1:(length(idx)-1)) {
          for (j in (i+1):length(idx)) {
            p1 <- idx[i]
            p2 <- idx[j]
            
            beta_mix_vec <- beta_base_vec
            beta_mix_vec[p1] <- beta_mix_vec[p1] + eps
            beta_mix_vec[p2] <- beta_mix_vec[p2] + eps
            beta_mix <- matrix(beta_mix_vec, nrow = k, byrow = TRUE)
            L_mix <- drw_log_lik(data, list(beta_mix, curr_sigma2, curr_tau, curr_rho))
            
            Hess_b[p1, p2] <- (L_mix - L_fwd[p1] - L_fwd[p2] + L_0) / (eps^2)
            Hess_b[p2, p1] <- Hess_b[p1, p2]
          }
        }
      }
    }
    
    post_prec <- prior_prec_beta - Hess_b
    post_prec <- (post_prec + t(post_prec)) / 2
    
    eigen_decomp <- eigen(post_prec, symmetric = TRUE)
    eigen_decomp$values <- pmax(eigen_decomp$values, 1e-10)
    
    post_cov <- eigen_decomp$vectors %*% diag(1 / eigen_decomp$values) %*% t(eigen_decomp$vectors)
    post_mean <- as.numeric(post_cov %*% (grad_b - Hess_b %*% beta_base_vec))
    
    sampled_beta <- as.numeric(MASS::mvrnorm(1, mu = post_mean, Sigma = post_cov))
    curr_beta <- matrix(sampled_beta, nrow = k, byrow = TRUE)
    
    # --- STEP 2: METROPOLIS-HASTINGS FOR SIGMA2 ---
    for (j in 1:k) {
      th_sig_p <- rnorm(1, mean = curr_th_sigma2[j], sd = log.sigma2.prop.scale[j])
      if (th_sig_p >= b_sig_low[j] && th_sig_p <= b_sig_upp[j]) {
        sig2_p <- exp(th_sig_p)
        prop_sigma2 <- curr_sigma2
        prop_sigma2[j] <- sig2_p
        
        l_ratio <- drw_log_lik(data, list(curr_beta, prop_sigma2, curr_tau, curr_rho)) - 
                   drw_log_lik(data, list(curr_beta, curr_sigma2, curr_tau, curr_rho))
        
        if (l_ratio > -rexp(1)) {
          curr_th_sigma2[j] <- th_sig_p
          curr_sigma2[j]    <- sig2_p
          sigma2.accept[iter, j] <- 1
        }
      }
      if (iter %% 100 == 0) {
        rate <- mean(sigma2.accept[(iter - 99):iter, j])
        scale.adj <- if (rate > 0.35) exp(min(0.1, 1 / sqrt(iter / 100))) else exp(-min(0.1, 1 / sqrt(iter / 100)))
        log.sigma2.prop.scale[j] <- log.sigma2.prop.scale[j] * scale.adj
      }
    }
    
    # --- STEP 3: METROPOLIS-HASTINGS FOR TAU ---
    for (j in 1:k) {
      th_tau_p <- rnorm(1, mean = curr_th_tau[j], sd = log.tau.prop.scale[j])
      if (th_tau_p >= b_tau_low[j] && th_tau_p <= b_tau_upp[j]) {
        tau_p <- exp(th_tau_p)
        prop_tau <- curr_tau
        prop_tau[j] <- tau_p
        
        l_ratio <- drw_log_lik(data, list(curr_beta, curr_sigma2, prop_tau, curr_rho)) - 
                   drw_log_lik(data, list(curr_beta, curr_sigma2, curr_tau, curr_rho))
        
        if (l_ratio > -rexp(1)) {
          curr_th_tau[j] <- th_tau_p
          curr_tau[j]    <- tau_p
          tau.accept[iter, j] <- 1
        }
      }
      if (iter %% 100 == 0) {
        rate <- mean(tau.accept[(iter - 99):iter, j])
        scale.adj <- if (rate > 0.35) exp(min(0.1, 1 / sqrt(iter / 100))) else exp(-min(0.1, 1 / sqrt(iter / 100)))
        log.tau.prop.scale[j] <- log.tau.prop.scale[j] * scale.adj
      }
    }
    
    # --- STEP 4: METROPOLIS-HASTINGS FOR RHO ---
    if (n.rho > 0) {
      for (j in 1:n.rho) {
        th_rho_p <- rnorm(1, mean = curr_th_rho[j], sd = rho.prop.scale[j])
        if (th_rho_p >= b_rho_low[j] && th_rho_p <= b_rho_upp[j]) {
          rho_p <- 2 * exp(th_rho_p) / (1 + exp(th_rho_p)) - 1
          prop_rho <- curr_rho
          prop_rho[j] <- rho_p
          
          l_ratio <- drw_log_lik(data, list(curr_beta, curr_sigma2, curr_tau, prop_rho)) - 
                     drw_log_lik(data, list(curr_beta, curr_sigma2, curr_tau, curr_rho))
          
          l_jacobian <- (th_rho_p - 2 * log(1 + exp(th_rho_p))) - 
                        (curr_th_rho[j] - 2 * log(1 + exp(curr_th_rho[j])))
          
          if (l_ratio + l_jacobian > -rexp(1)) {
            curr_th_rho[j] <- th_rho_p
            curr_rho[j]    <- rho_p
            rho.accept[iter, j] <- 1
          }
        }
        if (iter %% 100 == 0) {
          rate <- mean(rho.accept[(iter - 99):iter, j])
          scale.adj <- if (rate > 0.35) exp(min(0.1, 1 / sqrt(iter / 100))) else exp(-min(0.1, 1 / sqrt(iter / 100)))
          rho.prop.scale[j] <- rho.prop.scale[j] * scale.adj
        }
      }
    }
    
    if (iter > n.warm) {
      s_idx <- iter - n.warm
      beta_chain[s_idx, ]   <- as.vector(t(curr_beta))
      sigma2_chain[s_idx, ] <- curr_sigma2
      tau_chain[s_idx, ]    <- curr_tau
      if (n.rho > 0) rho_chain[s_idx, ] <- curr_rho
    }
  }
  
  return(list(
    beta = beta_chain, sigma = sqrt(sigma2_chain), tau = tau_chain, rho = rho_chain,
    sigma.accept.rate = colMeans(sigma2.accept[-seq_len(n.warm), , drop = FALSE]),
    tau.accept.rate   = colMeans(tau.accept[-seq_len(n.warm), , drop = FALSE]),
    rho.accept.rate   = if (n.rho > 0) colMeans(rho.accept[-seq_len(n.warm), , drop = FALSE]) else numeric(0)
  ))
}

# ====================================================================
# 3. ROBUST COMPILATION AND MASTER WRAPPER DRW INTERFACE
# ====================================================================
drw <- function(data1, data2=NULL, data3=NULL, data4=NULL, data5=NULL, 
                data6=NULL, data7=NULL, data8=NULL, data9=NULL, data10=NULL,
                n.datasets, method = "mle", poly.order = 1,
                bayes.n.burn = 3000, bayes.n.sample = 1000) {

  message(paste("Starting at: ", Sys.time()))
  k <- n.datasets
  n.rho <- k * (k - 1) / 2
  n_b_per_k <- poly.order + 1

  # Robust compilation preventing column renaming collisions
  dat <- vector(mode = "list", length = k)
  for (i in 1 : k) {
    eval(parse(text = paste0("data.temp <- data", i)))
    data.temp <- as.data.frame(data.temp)
    colnames(data.temp)[1] <- "V1"
    colnames(data.temp)[2] <- paste0("Close_", i)
    colnames(data.temp)[3] <- paste0("Daily_Volatility_", i)
    dat[[i]] <- data.temp
  }

  data.comb <- dat[[1]]
  if (k > 1) {
    for (i in 2:k) {
      data.comb <- merge(data.comb, dat[[i]], by = "V1", all = TRUE)
    }
  }
  data.comb <- as.matrix(data.comb)

# ====================================================================
  # FIXED STABILIZED MASTER WRAPPER (PREVENTS INITIALIZATION -INF CRASH)
  # ====================================================================
  drw_log_lik_optim <- function(th, k, n_b_per_k, data) {
    beta <- matrix(th[1 : (n_b_per_k * k)], nrow = k, byrow = TRUE)
    sigma2 <- exp(th[(n_b_per_k * k + 1) : ((n_b_per_k + 1) * k)])
    tau <- exp(th[((n_b_per_k + 1) * k + 1) : ((n_b_per_k + 2) * k)])
    if (n.rho > 0) {
      th_rho <- th[((n_b_per_k + 2) * k + 1) : ((n_b_per_k + 2) * k + n.rho)]
      rho <- 2 * exp(th_rho) / (1 + exp(th_rho)) - 1
    } else {
      rho <- numeric(0)
    }
    
    val <- drw_log_lik(data, list(beta, sigma2, tau, rho))
    
    # Safety catch for optim: replace literal -Inf with a large finite penalty
    if (is.infinite(val) || is.na(val)) return(-1e10)
    return(val)
  }

  raw_t <- data.comb[, 1]
  raw_t_range <- max(raw_t) - min(raw_t)
  if (!is.finite(raw_t_range) || raw_t_range <= 0) {
    stop("The observation times must contain at least two distinct finite values.")
  }
  norm_t <- (raw_t - min(raw_t)) / raw_t_range
  beta_mat_init <- matrix(0, nrow = k, ncol = n_b_per_k)
  beta_design <- outer(norm_t, 0:poly.order, `^`)

  for (i in 1:k) {
    asset_price <- data.comb[, 2 * i]
    keep <- is.finite(asset_price) & is.finite(norm_t)
    if (sum(keep) >= n_b_per_k) {
      fit <- lm.fit(x = beta_design[keep, , drop = FALSE], y = asset_price[keep])
      beta_mat_init[i, ] <- fit$coefficients
      beta_mat_init[i, !is.finite(beta_mat_init[i, ])] <- 0
    } else {
      beta_mat_init[i, 1] <- mean(asset_price, na.rm = TRUE)
      if (!is.finite(beta_mat_init[i, 1])) beta_mat_init[i, 1] <- 0
    }
  }
  beta_init <- as.vector(t(beta_mat_init))
  
  # Extract and protect variance estimates from 0/NaN anomalies
  init_meas_sd <- colMeans(data.comb[, seq(3, 2 * k + 1, by = 2), drop = FALSE], na.rm = TRUE)
  init_meas_sd[is.na(init_meas_sd) | init_meas_sd <= 0] <- 1e-4 # Safety Floor
  
  # Initialize rho parameters to 0.01 (transformed space) to reinforce positive definiteness
  init_th_rho <- rep(log((0.01 + 1) / (1 - 0.01)), n.rho)

  # Construct stable initial parameter array
  initial.temp <- c(beta_init, 
                    2 * log(init_meas_sd), 
                    log(rep(100, k)), 
                    init_th_rho)

  n_beta <- n_b_per_k * k  
  lower_bounds <- c(rep(-Inf, n_beta), rep(-20, k), rep(-15, k), rep(-10, n.rho))     
  upper_bounds <- c(rep(Inf, n_beta),  rep(30, k),  rep(20, k),  rep(10, n.rho))      

  opt.temp <- optim(initial.temp, drw_log_lik_optim, 
                    control = list(fnscale = -1, factr = 1e7), 
                    method = "L-BFGS-B", lower = lower_bounds, upper = upper_bounds,
                    hessian = TRUE, k = k, n_b_per_k = n_b_per_k, data = data.comb)

  rho.mle <- if (n.rho > 0) {
    th_rho_mle <- opt.temp$par[((n_b_per_k + 2) * k + 1) : ((n_b_per_k + 2) * k + n.rho)]
    as.numeric(2 * exp(th_rho_mle) / (1 + exp(th_rho_mle)) - 1)
  } else {
    numeric(0)
  }

  initial.mle <- list(beta   = as.numeric(opt.temp$par[1 : (n_b_per_k * k)]), 
                      sigma2 = as.numeric(exp(opt.temp$par[(n_b_per_k * k + 1) : ((n_b_per_k + 1) * k)])), 
                      tau    = as.numeric(exp(opt.temp$par[((n_b_per_k + 1) * k + 1) : ((n_b_per_k + 2) * k)])), 
                      rho    = rho.mle)

  if (method == "bayes") {
    res <- bayes(data = data.comb, theta = initial.mle, 
                 n.warm = bayes.n.burn, n.sample = bayes.n.sample, 
                 k = k, n_b_per_k = n_b_per_k, 
                 lower_bounds = lower_bounds, upper_bounds = upper_bounds)
    res$tau.days <- res$tau * raw_t_range
    res$time.range <- raw_t_range
    res$time.min <- min(raw_t)
    res$data.comb <- data.comb
  } else {
    res <- initial.mle
    res$sigma <- sqrt(res$sigma2)
    res$tau.days <- res$tau * raw_t_range
    res$time.range <- raw_t_range
    res$time.min <- min(raw_t)
    res$data.comb <- data.comb
  }

  message(paste("Ending at: ", Sys.time()))
  return(res)
}
# ====================================================================
# 4. SIMULATION FUNCTION
# ====================================================================
drw.sim <- function(time, n.datasets, measure.error.SD = NULL,
                    mu, sigma, tau, rho = NULL) {
  k <- n.datasets
  n <- length(time)

  if (k < 1) stop("'n.datasets' must be a positive integer.")
  if (length(mu) != k || length(sigma) != k || length(tau) != k) {
    stop("'mu', 'sigma', and 'tau' must each have length 'n.datasets'.")
  }

  if (k == 1) {
    if (is.null(measure.error.SD)) {
      measure.error.SD <- rep(0, n)
    }
    if (length(measure.error.SD) != n) {
      stop("For one time series, 'measure.error.SD' must have length equal to 'time'.")
    }

    delta.t <- diff(time)
    a.i <- exp(-delta.t / tau)

    X <- rep(NA_real_, n)
    X[1] <- rnorm(1, mean = mu, sd = sigma * sqrt(tau / 2))
    for (i in 2:n) {
      X[i] <- rnorm(1,
                    mean = mu + a.i[i - 1] * (X[i - 1] - mu),
                    sd = sigma * sqrt(tau * (1 - a.i[i - 1]^2) / 2))
    }

    x <- rnorm(n, mean = X, sd = measure.error.SD)
  } else {
    if (is.null(measure.error.SD)) {
      measure.error.SD <- matrix(0, nrow = n, ncol = k)
    }
    measure.error.SD <- as.matrix(measure.error.SD)
    if (!all(dim(measure.error.SD) == c(n, k))) {
      stop("For multiple time series, 'measure.error.SD' must be an n by k matrix.")
    }

    n.rho <- k * (k - 1) / 2
    if (is.null(rho) || length(rho) != n.rho) {
      stop("For multiple time series, 'rho' must have length k * (k - 1) / 2.")
    }

    rho.mat <- matrix(1, nrow = k, ncol = k)
    rho.mat[upper.tri(rho.mat)] <- rho
    rho.mat[lower.tri(rho.mat)] <- t(rho.mat)[lower.tri(rho.mat)]

    det_rho <- det(rho.mat)
    if (is.na(det_rho) || det_rho <= 0) {
      stop("The correlation matrix implied by 'rho' must be positive definite.")
    }

    delta.t <- diff(time)
    a.i <- exp(-delta.t %*% t(1 / tau))

    X <- matrix(NA_real_, nrow = n, ncol = k)
    Q <- vector("list", n)
    Q[[1]] <- t(rho.mat * sigma) * sigma
    temp <- outer(1 / tau, 1 / tau, "+")
    Q[[1]] <- Q[[1]] / temp

    X[1, ] <- MASS::mvrnorm(1, mu = mu, Sigma = Q[[1]])

    for (i in 2:n) {
      M.i <- mu + a.i[i - 1, ] * (X[i - 1, ] - mu)
      Q[[i]] <- Q[[1]] * (1 - exp(-temp * delta.t[i - 1]))
      X[i, ] <- MASS::mvrnorm(1, mu = M.i, Sigma = Q[[i]])
    }

    x <- matrix(rnorm(n * k, mean = as.numeric(X), sd = as.numeric(measure.error.SD)),
                nrow = n, ncol = k)
  }

  return(x)
}
