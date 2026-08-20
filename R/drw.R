# ====================================================================
# 1. KALMAN SUFFICIENT STATISTICS FOR LINEAR MEAN PARAMETERS
# ====================================================================

# The polynomial mean coefficients enter the model linearly.  Conditional on
# the DRW covariance parameters, the Kalman innovations can therefore be
# written as y_i - c_i - D_i beta.  A single Kalman pass accumulates the
# Gaussian quadratic-form sufficient statistics in beta.  This permits exact
# profiling for MLE and an exact Gaussian conditional update for Bayesian
# sampling without forming the full observation covariance matrix.

drw_filter_suff <- function(data, sigma2, tau, rho_values, n_b_per_k) {
  data <- as.matrix(data)
  k <- length(sigma2)
  n_beta <- k * n_b_per_k

  if (length(tau) != k || any(!is.finite(sigma2)) || any(sigma2 <= 0) ||
      any(!is.finite(tau)) || any(tau <= 0)) {
    return(list(valid = FALSE))
  }

  rho <- matrix(1, nrow = k, ncol = k)
  if (k > 1) {
    if (length(rho_values) != k * (k - 1) / 2 || any(!is.finite(rho_values))) {
      return(list(valid = FALSE))
    }
    rho[upper.tri(rho)] <- rho_values
    rho[lower.tri(rho)] <- t(rho)[lower.tri(rho)]
  }

  chol_rho <- tryCatch(chol(rho), error = function(e) NULL)
  if (is.null(chol_rho)) return(list(valid = FALSE))

  raw.time <- data[, 1]
  time.range <- max(raw.time) - min(raw.time)
  if (!is.finite(time.range) || time.range <= 0) {
    stop("The observation times must contain at least two distinct finite values.")
  }

  time.comb <- (raw.time - min(raw.time)) / time.range
  leng.time <- length(time.comb)
  p_order <- n_b_per_k - 1

  B <- outer(time.comb, 0:p_order, `^`)
  if (n_b_per_k == 1) B <- matrix(B, ncol = 1)

  # M[[t]] maps the complete beta vector to the k-dimensional mean at time t.
  M <- vector("list", leng.time)
  for (tt in seq_len(leng.time)) {
    Mt <- matrix(0, nrow = k, ncol = n_beta)
    for (j in seq_len(k)) {
      idx <- ((j - 1) * n_b_per_k + 1):(j * n_b_per_k)
      Mt[j, idx] <- B[tt, ]
    }
    M[[tt]] <- Mt
  }

  lc.comb <- data[, seq(2, 2 * k, by = 2), drop = FALSE]
  var.lc.comb <- data[, seq(3, 2 * k + 1, by = 2), drop = FALSE]^2

  inv_tau <- 1 / tau
  temp <- outer(inv_tau, inv_tau, "+")
  Sigma0 <- rho * outer(sqrt(sigma2), sqrt(sigma2)) / temp
  Sigma0 <- (Sigma0 + t(Sigma0)) / 2

  delta.t <- diff(time.comb)
  a.i <- if (leng.time > 1) exp(-outer(delta.t, inv_tau, "*")) else matrix(numeric(0), 0, k)

  Sigma_prior <- Sigma0
  Sigma_post <- Sigma0

  # Affine state mean: c + D beta.
  c_prior <- numeric(k)
  D_prior <- M[[1]]
  c_post <- c_prior
  D_post <- D_prior

  A <- matrix(0, nrow = n_beta, ncol = n_beta)
  b <- numeric(n_beta)
  cquad <- 0
  logdet <- 0
  n_obs <- 0L

  for (tt in seq_len(leng.time)) {
    if (tt > 1) {
      a <- a.i[tt - 1, ]
      Sigma_prior <- (a %o% a) * Sigma_post +
        Sigma0 * (1 - exp(-temp * delta.t[tt - 1]))
      Sigma_prior <- (Sigma_prior + t(Sigma_prior)) / 2

      c_prior <- a * c_post
      D_prior <- M[[tt]] + a * (D_post - M[[tt - 1]])
    }

    lc_row <- lc.comb[tt, ]
    q <- which(!is.na(lc_row))
    len_q <- length(q)

    if (len_q == 0) {
      Sigma_post <- Sigma_prior
      c_post <- c_prior
      D_post <- D_prior
      next
    }

    lc.t <- lc_row[q]
    var.t <- var.lc.comb[tt, q]
    if (any(!is.finite(lc.t)) || any(!is.finite(var.t)) || any(var.t < 0)) {
      return(list(valid = FALSE))
    }

    Qt <- Sigma_prior[q, q, drop = FALSE] + diag(var.t, nrow = len_q)
    Qt <- (Qt + t(Qt)) / 2
    chol_Qt <- tryCatch(chol(Qt), error = function(e) NULL)
    if (is.null(chol_Qt)) return(list(valid = FALSE))
    invQt <- chol2inv(chol_Qt)

    y0 <- as.numeric(lc.t - c_prior[q])
    Dq <- D_prior[q, , drop = FALSE]

    A <- A + crossprod(Dq, invQt %*% Dq)
    b <- b + as.numeric(crossprod(Dq, invQt %*% y0))
    cquad <- cquad + sum(y0 * as.numeric(invQt %*% y0))
    logdet <- logdet + 2 * sum(log(diag(chol_Qt)))
    n_obs <- n_obs + len_q

    K_gain <- Sigma_prior[, q, drop = FALSE] %*% invQt
    Sigma_post <- Sigma_prior - K_gain %*% Sigma_prior[q, , drop = FALSE]
    Sigma_post <- (Sigma_post + t(Sigma_post)) / 2

    c_post <- as.numeric(c_prior + K_gain %*% y0)
    D_post <- D_prior - K_gain %*% Dq
  }

  A <- (A + t(A)) / 2

  list(
    valid = TRUE,
    A = A,
    b = b,
    cquad = as.numeric(cquad),
    logdet = as.numeric(logdet),
    n_obs = as.integer(n_obs),
    n_beta = n_beta,
    k = k,
    n_b_per_k = n_b_per_k,
    time.range = time.range
  )
}


drw_log_lik_from_suff <- function(suff, beta) {
  if (is.null(suff$valid) || !isTRUE(suff$valid)) return(-Inf)
  beta <- as.numeric(beta)
  if (length(beta) != suff$n_beta || any(!is.finite(beta))) return(-Inf)

  quad <- suff$cquad - 2 * sum(beta * suff$b) +
    sum(beta * as.numeric(suff$A %*% beta))
  if (!is.finite(quad)) return(-Inf)

  -0.5 * (suff$n_obs * log(2 * pi) + suff$logdet + quad)
}


drw_profile_from_suff <- function(suff) {
  if (is.null(suff$valid) || !isTRUE(suff$valid)) {
    return(list(loglik = -Inf, beta = rep(NA_real_, suff$n_beta %||% 0L)))
  }

  chol_A <- tryCatch(chol(suff$A), error = function(e) NULL)
  if (is.null(chol_A)) {
    return(list(loglik = -Inf, beta = rep(NA_real_, suff$n_beta)))
  }

  beta_hat <- backsolve(chol_A, forwardsolve(t(chol_A), suff$b))
  quad <- suff$cquad - sum(suff$b * beta_hat)
  if (!is.finite(quad) || quad < -1e-7) {
    return(list(loglik = -Inf, beta = rep(NA_real_, suff$n_beta)))
  }
  quad <- max(quad, 0)

  loglik <- -0.5 * (suff$n_obs * log(2 * pi) + suff$logdet + quad)
  list(loglik = as.numeric(loglik), beta = as.numeric(beta_hat))
}


sample_beta_conditional <- function(suff, prior_precision = 1e-6) {
  if (is.null(suff$valid) || !isTRUE(suff$valid)) {
    stop("Invalid Kalman sufficient statistics for beta update.")
  }

  P <- suff$A + diag(prior_precision, suff$n_beta)
  P <- (P + t(P)) / 2
  chol_P <- tryCatch(chol(P), error = function(e) NULL)
  if (is.null(chol_P)) stop("Conditional beta precision matrix is not positive definite.")

  post_mean <- backsolve(chol_P, forwardsolve(t(chol_P), suff$b))
  # If P = R'R and z ~ N(0,I), then R^{-1}z has covariance P^{-1}.
  draw <- as.numeric(post_mean + backsolve(chol_P, rnorm(suff$n_beta)))
  draw
}


`%||%` <- function(x, y) if (is.null(x) || length(x) == 0) y else x


# ====================================================================
# 2. LOG-LIKELIHOOD WITH EXPLICIT BETA (INTERNAL BACKWARD COMPATIBILITY)
# ====================================================================

drw_log_lik <- function(data, theta) {
  beta <- theta[[1]]
  if (is.null(dim(beta))) stop("theta[[1]] must be a beta matrix.")
  k <- nrow(beta)
  n_b_per_k <- ncol(beta)
  sigma2 <- theta[[2]]
  tau <- theta[[3]]
  rho_values <- theta[[4]]

  if (length(sigma2) != k || length(tau) != k) return(-Inf)

  suff <- drw_filter_suff(
    data = data,
    sigma2 = sigma2,
    tau = tau,
    rho_values = rho_values,
    n_b_per_k = n_b_per_k
  )

  drw_log_lik_from_suff(suff, as.vector(t(beta)))
}


# ====================================================================
# 3. BAYESIAN SAMPLER
#    - exact Gaussian conditional update for beta
#    - cached current likelihood / Kalman sufficient statistics
# ====================================================================

bayes <- function(data, theta, n.warm, n.sample, k, n_b_per_k,
                  lower_bounds, upper_bounds) {

  n.total <- n.warm + n.sample
  n.rho <- k * (k - 1) / 2
  n_beta <- k * n_b_per_k

  beta_chain <- matrix(0, nrow = n.sample, ncol = n_beta)
  sigma2_chain <- matrix(0, nrow = n.sample, ncol = k)
  tau_chain <- matrix(0, nrow = n.sample, ncol = k)
  rho_chain <- matrix(0, nrow = n.sample, ncol = n.rho)

  sigma2.accept <- matrix(0, nrow = n.total, ncol = k)
  tau.accept <- matrix(0, nrow = n.total, ncol = k)
  rho.accept <- matrix(0, nrow = n.total, ncol = n.rho)

  curr_beta <- matrix(theta$beta, nrow = k, byrow = TRUE)
  curr_sigma2 <- theta$sigma2
  curr_tau <- theta$tau
  curr_rho <- theta$rho

  curr_th_sigma2 <- log(curr_sigma2)
  curr_th_tau <- log(curr_tau)
  curr_th_rho <- if (n.rho > 0) 2 * atanh(curr_rho) else numeric(0)

  b_sig_low <- lower_bounds[seq_len(k)]
  b_sig_upp <- upper_bounds[seq_len(k)]
  b_tau_low <- lower_bounds[k + seq_len(k)]
  b_tau_upp <- upper_bounds[k + seq_len(k)]
  if (n.rho > 0) {
    b_rho_low <- lower_bounds[2 * k + seq_len(n.rho)]
    b_rho_upp <- upper_bounds[2 * k + seq_len(n.rho)]
  } else {
    b_rho_low <- numeric(0)
    b_rho_upp <- numeric(0)
  }

  log.sigma2.prop.scale <- rep(0.05, k)
  log.tau.prop.scale <- rep(0.1, k)
  rho.prop.scale <- rep(0.05, n.rho)

  prior_prec_beta <- 1e-6

  curr_suff <- drw_filter_suff(
    data, curr_sigma2, curr_tau, curr_rho, n_b_per_k
  )
  if (!isTRUE(curr_suff$valid)) stop("Invalid initial covariance parameters for Bayesian sampling.")
  curr_loglik <- drw_log_lik_from_suff(curr_suff, as.vector(t(curr_beta)))

  message("Running Bayesian MCMC Posterior Sampling...")

  for (iter in seq_len(n.total)) {

    # --- STEP 1: EXACT GAUSSIAN CONDITIONAL UPDATE FOR BETA ---
    sampled_beta <- sample_beta_conditional(curr_suff, prior_prec_beta)
    curr_beta <- matrix(sampled_beta, nrow = k, byrow = TRUE)
    curr_loglik <- drw_log_lik_from_suff(curr_suff, sampled_beta)

    # --- STEP 2: METROPOLIS-HASTINGS FOR SIGMA2 ---
    for (j in seq_len(k)) {
      th_sig_p <- rnorm(1, mean = curr_th_sigma2[j], sd = log.sigma2.prop.scale[j])
      if (th_sig_p >= b_sig_low[j] && th_sig_p <= b_sig_upp[j]) {
        prop_sigma2 <- curr_sigma2
        prop_sigma2[j] <- exp(th_sig_p)

        prop_suff <- drw_filter_suff(data, prop_sigma2, curr_tau, curr_rho, n_b_per_k)
        prop_loglik <- drw_log_lik_from_suff(prop_suff, sampled_beta)
        l_ratio <- prop_loglik - curr_loglik

        if (is.finite(l_ratio) && l_ratio > -rexp(1)) {
          curr_th_sigma2[j] <- th_sig_p
          curr_sigma2 <- prop_sigma2
          curr_suff <- prop_suff
          curr_loglik <- prop_loglik
          sigma2.accept[iter, j] <- 1
        }
      }

      if (iter %% 100 == 0) {
        rate <- mean(sigma2.accept[(iter - 99):iter, j])
        adj <- min(0.1, 1 / sqrt(iter / 100))
        scale.adj <- if (rate > 0.35) exp(adj) else exp(-adj)
        log.sigma2.prop.scale[j] <- log.sigma2.prop.scale[j] * scale.adj
      }
    }

    # --- STEP 3: METROPOLIS-HASTINGS FOR TAU ---
    for (j in seq_len(k)) {
      th_tau_p <- rnorm(1, mean = curr_th_tau[j], sd = log.tau.prop.scale[j])
      if (th_tau_p >= b_tau_low[j] && th_tau_p <= b_tau_upp[j]) {
        prop_tau <- curr_tau
        prop_tau[j] <- exp(th_tau_p)

        prop_suff <- drw_filter_suff(data, curr_sigma2, prop_tau, curr_rho, n_b_per_k)
        prop_loglik <- drw_log_lik_from_suff(prop_suff, sampled_beta)
        l_ratio <- prop_loglik - curr_loglik

        if (is.finite(l_ratio) && l_ratio > -rexp(1)) {
          curr_th_tau[j] <- th_tau_p
          curr_tau <- prop_tau
          curr_suff <- prop_suff
          curr_loglik <- prop_loglik
          tau.accept[iter, j] <- 1
        }
      }

      if (iter %% 100 == 0) {
        rate <- mean(tau.accept[(iter - 99):iter, j])
        adj <- min(0.1, 1 / sqrt(iter / 100))
        scale.adj <- if (rate > 0.35) exp(adj) else exp(-adj)
        log.tau.prop.scale[j] <- log.tau.prop.scale[j] * scale.adj
      }
    }

    # --- STEP 4: METROPOLIS-HASTINGS FOR RHO ---
    if (n.rho > 0) {
      for (j in seq_len(n.rho)) {
        th_rho_p <- rnorm(1, mean = curr_th_rho[j], sd = rho.prop.scale[j])
        if (th_rho_p >= b_rho_low[j] && th_rho_p <= b_rho_upp[j]) {
          prop_rho <- curr_rho
          prop_rho[j] <- tanh(th_rho_p / 2)

          prop_suff <- drw_filter_suff(data, curr_sigma2, curr_tau, prop_rho, n_b_per_k)
          prop_loglik <- drw_log_lik_from_suff(prop_suff, sampled_beta)
          l_ratio <- prop_loglik - curr_loglik

          # The additive constant in the Jacobian cancels in the ratio.
          l_jacobian <- -2 * log(cosh(th_rho_p / 2)) +
                         2 * log(cosh(curr_th_rho[j] / 2))

          if (is.finite(l_ratio) && l_ratio + l_jacobian > -rexp(1)) {
            curr_th_rho[j] <- th_rho_p
            curr_rho <- prop_rho
            curr_suff <- prop_suff
            curr_loglik <- prop_loglik
            rho.accept[iter, j] <- 1
          }
        }

        if (iter %% 100 == 0) {
          rate <- mean(rho.accept[(iter - 99):iter, j])
          adj <- min(0.1, 1 / sqrt(iter / 100))
          scale.adj <- if (rate > 0.35) exp(adj) else exp(-adj)
          rho.prop.scale[j] <- rho.prop.scale[j] * scale.adj
        }
      }
    }

    if (iter > n.warm) {
      s_idx <- iter - n.warm
      beta_chain[s_idx, ] <- as.vector(t(curr_beta))
      sigma2_chain[s_idx, ] <- curr_sigma2
      tau_chain[s_idx, ] <- curr_tau
      if (n.rho > 0) rho_chain[s_idx, ] <- curr_rho
    }
  }

  saved_iter <- (n.warm + 1):n.total

  list(
    beta = beta_chain,
    sigma = sqrt(sigma2_chain),
    tau = tau_chain,
    rho = rho_chain,
    sigma.accept.rate = colMeans(sigma2.accept[saved_iter, , drop = FALSE]),
    tau.accept.rate = colMeans(tau.accept[saved_iter, , drop = FALSE]),
    rho.accept.rate = if (n.rho > 0) {
      colMeans(rho.accept[saved_iter, , drop = FALSE])
    } else numeric(0)
  )
}


# ====================================================================
# 4. MASTER WRAPPER DRW INTERFACE
# ====================================================================

drw <- function(data1, data2 = NULL, data3 = NULL, data4 = NULL, data5 = NULL,
                data6 = NULL, data7 = NULL, data8 = NULL, data9 = NULL, data10 = NULL,
                n.datasets, method = "mle", poly.order = 1,
                bayes.n.burn = 3000, bayes.n.sample = 1000) {

  message(paste("Starting at: ", Sys.time()))

  if (length(n.datasets) != 1 || !is.finite(n.datasets) ||
      n.datasets != as.integer(n.datasets) || n.datasets < 1 || n.datasets > 10) {
    stop("'n.datasets' must be an integer from 1 to 10.")
  }
  if (length(poly.order) != 1 || !is.finite(poly.order) ||
      poly.order != as.integer(poly.order) || poly.order < 0) {
    stop("'poly.order' must be a nonnegative integer.")
  }
  method <- match.arg(method, c("mle", "bayes"))
  if (length(bayes.n.burn) != 1 || !is.finite(bayes.n.burn) ||
      bayes.n.burn != as.integer(bayes.n.burn) || bayes.n.burn < 0) {
    stop("'bayes.n.burn' must be a nonnegative integer.")
  }
  if (length(bayes.n.sample) != 1 || !is.finite(bayes.n.sample) ||
      bayes.n.sample != as.integer(bayes.n.sample) || bayes.n.sample < 1) {
    stop("'bayes.n.sample' must be a positive integer.")
  }

  k <- as.integer(n.datasets)
  poly.order <- as.integer(poly.order)
  n.rho <- k * (k - 1) / 2
  n_b_per_k <- poly.order + 1

  # Robust compilation preventing column-renaming collisions.
  data_args <- list(data1, data2, data3, data4, data5,
                    data6, data7, data8, data9, data10)
  dat <- vector("list", k)
  for (i in seq_len(k)) {
    if (is.null(data_args[[i]])) stop("A requested data set is NULL: data", i, ".")
    data.temp <- as.data.frame(data_args[[i]])
    if (ncol(data.temp) < 3) stop("Each data set must contain at least three columns.")
    data.temp <- data.temp[, 1:3, drop = FALSE]
    colnames(data.temp) <- c(
      "V1", paste0("Close_", i), paste0("Daily_Volatility_", i)
    )
    dat[[i]] <- data.temp
  }

  data.comb <- dat[[1]]
  if (k > 1) {
    for (i in 2:k) {
      data.comb <- merge(data.comb, dat[[i]], by = "V1", all = TRUE)
    }
  }
  data.comb <- as.matrix(data.comb)
  data.comb <- data.comb[order(data.comb[, 1]), , drop = FALSE]

  raw_t <- data.comb[, 1]
  raw_t_range <- max(raw_t) - min(raw_t)
  if (!is.finite(raw_t_range) || raw_t_range <= 0) {
    stop("The observation times must contain at least two distinct finite values.")
  }

  # Initial covariance parameters.  Beta is not part of the numerical optimizer;
  # it is solved exactly by conditional GLS for every covariance proposal.
  init_meas_sd <- colMeans(
    data.comb[, seq(3, 2 * k + 1, by = 2), drop = FALSE],
    na.rm = TRUE
  )
  init_meas_sd[!is.finite(init_meas_sd) | init_meas_sd <= 0] <- 1e-4

  init_th_rho <- rep(2 * atanh(0.01), n.rho)
  initial.temp <- c(
    2 * log(init_meas_sd),
    log(rep(100, k)),
    init_th_rho
  )

  lower_bounds <- c(rep(-20, k), rep(-15, k), rep(-10, n.rho))
  upper_bounds <- c(rep(30, k), rep(20, k), rep(10, n.rho))

  drw_profile_log_lik_optim <- function(th, k, n_b_per_k, data) {
    sigma2 <- exp(th[seq_len(k)])
    tau <- exp(th[k + seq_len(k)])
    rho_values <- if (n.rho > 0) {
      tanh(th[2 * k + seq_len(n.rho)] / 2)
    } else numeric(0)

    suff <- drw_filter_suff(data, sigma2, tau, rho_values, n_b_per_k)
    prof <- drw_profile_from_suff(suff)
    val <- prof$loglik
    if (!is.finite(val)) -1e10 else val
  }

  opt.temp <- optim(
    initial.temp,
    drw_profile_log_lik_optim,
    control = list(fnscale = -1, factr = 1e7),
    method = "L-BFGS-B",
    lower = lower_bounds,
    upper = upper_bounds,
    hessian = TRUE,
    k = k,
    n_b_per_k = n_b_per_k,
    data = data.comb
  )

  sigma2.mle <- exp(opt.temp$par[seq_len(k)])
  tau.mle <- exp(opt.temp$par[k + seq_len(k)])
  rho.mle <- if (n.rho > 0) {
    tanh(opt.temp$par[2 * k + seq_len(n.rho)] / 2)
  } else numeric(0)

  mle_suff <- drw_filter_suff(
    data.comb, sigma2.mle, tau.mle, rho.mle, n_b_per_k
  )
  mle_profile <- drw_profile_from_suff(mle_suff)
  if (!is.finite(mle_profile$loglik)) {
    stop("The final profiled likelihood could not be evaluated.")
  }

  initial.mle <- list(
    beta = mle_profile$beta,
    sigma2 = as.numeric(sigma2.mle),
    tau = as.numeric(tau.mle),
    rho = as.numeric(rho.mle)
  )

  if (method == "bayes") {
    res <- bayes(
      data = data.comb,
      theta = initial.mle,
      n.warm = bayes.n.burn,
      n.sample = bayes.n.sample,
      k = k,
      n_b_per_k = n_b_per_k,
      lower_bounds = lower_bounds,
      upper_bounds = upper_bounds
    )
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
    res$logLik <- mle_profile$loglik
    res$convergence <- opt.temp$convergence
  }

  message(paste("Ending at: ", Sys.time()))
  res
}

# ====================================================================
# 5. SIMULATION FUNCTION
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
