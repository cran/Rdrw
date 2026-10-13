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
  curr_R <- diag(k)
  if (n.rho > 0) {
    curr_R[upper.tri(curr_R)] <- curr_rho
    curr_R[lower.tri(curr_R)] <- t(curr_R)[lower.tri(curr_R)]
  }
  curr_th_rho <- drw_z_from_corr(curr_R)

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
          prop_z <- curr_th_rho
          prop_z[j] <- th_rho_p
          prop_rho <- drw_corr_from_z(prop_z, k)

          prop_suff <- drw_filter_suff(data, curr_sigma2, curr_tau, prop_rho, n_b_per_k)
          prop_loglik <- drw_log_lik_from_suff(prop_suff, sampled_beta)
          l_ratio <- prop_loglik - curr_loglik

          # Symmetric random walk with uniform prior on bounded z;
          # no Jacobian correction is needed in this parameterization.
          if (is.finite(l_ratio) && l_ratio > -rexp(1)) {
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
    sigma2 = sigma2_chain,
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

# Correlation matrix from unconstrained row-wise partial correlations.
# The Cholesky construction guarantees positive definiteness.
drw_corr_from_z <- function(z, k) {
  L <- diag(k)
  if (k > 1L) {
    ix <- 1L
    for (i in 2:k) {
      remain <- 1
      for (j in seq_len(i - 1L)) {
        a <- tanh(z[ix])
        L[i, j] <- a * remain
        remain <- remain * sqrt(1 - a^2)
        ix <- ix + 1L
      }
      L[i, i] <- remain
    }
  }
  R <- tcrossprod(L)
  as.numeric(R[upper.tri(R)])
}


# Convert a positive-definite correlation matrix to unconstrained partial
# correlations, inverse of drw_corr_from_z().
drw_z_from_corr <- function(R) {
  k <- nrow(R)
  if (k == 1L) return(numeric(0))
  L <- t(chol(R))
  z <- numeric(k * (k - 1L) / 2L)
  ix <- 1L
  for (i in 2:k) {
    remain <- 1
    for (j in seq_len(i - 1L)) {
      a <- max(-1 + 1e-10, min(1 - 1e-10, L[i,j] / remain))
      z[ix] <- atanh(a)
      remain <- remain * sqrt(1 - a^2)
      ix <- ix + 1L
    }
  }
  z
}

# Cheap, observation-adaptive marginal OU likelihood optimizations.
# All internal timescales and diffusion variances use normalized time.
drw_univariate_warm <- function(dat, time.range, n_b_per_k,
                                tau.override = NULL, maxit = 500L) {
  tt <- dat[,1]; yy <- dat[,2]; ee <- dat[,3]
  ok <- is.finite(tt) & is.finite(yy) & is.finite(ee) & ee >= 0
  tt <- tt[ok]; yy <- yy[ok]; ee <- ee[ok]
  if (length(tt) < max(3L, n_b_per_k + 1L)) return(NULL)
  ord <- order(tt); tt <- tt[ord]; yy <- yy[ord]; ee <- ee[ord]
  d <- diff(sort(unique(tt)))
  d <- d[d > 0 & is.finite(d)]
  if (!length(d)) return(NULL)
  span <- max(tt) - min(tt)
  cadence <- as.numeric(stats::quantile(d, .5, names = FALSE))
  low <- max(min(d), cadence / 2, span * 1e-5)
  high <- max(low * 1.01, span)
  if (!is.null(tau.override)) {
    starts_tau <- rep(tau.override, 3L)
  } else {
    starts_tau <- c(sqrt(low * high), low * (high / low)^.25,
                    low * (high / low)^.75)
  }
  v <- stats::var(yy) - mean(ee^2)
  if (!is.finite(v) || v <= 1e-10) v <- stats::var(yy)
  if (!is.finite(v) || v <= 0) v <- 1e-6
  dd <- cbind(tt, yy, ee)
  obj <- function(par) {
    tau <- exp(par[2]); sig2 <- 2 * exp(par[1]) / tau
    pr <- drw_profile_from_suff(drw_filter_suff(dd, sig2, tau,
                                                  numeric(0), n_b_per_k))
    if (is.finite(pr$loglik)) -pr$loglik else 1e12
  }
  lo <- c(-25, log(1e-5)); hi <- c(25, log(1e4))
  candidates <- lapply(starts_tau, function(tau) {
    par <- c(log(v), log(tau / span))
    par <- pmax(lo, pmin(hi, par))
    tryCatch(stats::optim(par, obj, method = 'L-BFGS-B', lower = lo,
      upper = hi, control = list(maxit = maxit)),
      error = function(e) list(value = Inf, convergence = 999L))
  })
  val <- vapply(candidates, function(x) x$value, numeric(1))
  if (!any(is.finite(val) & val < 1e11)) return(NULL)
  best <- candidates[[which.min(val)]]
  tau <- exp(best$par[2]); sig2 <- 2 * exp(best$par[1]) / tau
  list(tau = tau * span / time.range, sigma2 = sig2 * time.range / span, convergence = best$convergence,
       logLik = -best$value, cadence = cadence, baseline = span)
}

# Standardized marginal one-step prediction innovations at observed times.
# At asynchronous times only exactly overlapping innovations are paired.
drw_innovation_corr_start <- function(data, tau, sigma2, beta, k,
                                      n_b_per_k, shrink = .25) {
  if (k < 2L) return(matrix(1, 1, 1))
  t <- data[,1]; span <- max(t)-min(t); u <- (t-min(t))/span
  innov <- matrix(NA_real_, nrow(data), k)
  for (j in seq_len(k)) {
    y <- data[,2*j]; e <- data[,2*j+1]
    ok <- which(is.finite(y) & is.finite(e) & e>=0)
    if (length(ok) < 3L) next
    bj <- beta[((j-1)*n_b_per_k+1):(j*n_b_per_k)]
    mu <- as.numeric(outer(u, 0:(n_b_per_k-1), `^`) %*% bj)
    v <- sigma2[j]*tau[j]/2; state <- 0; P <- v
    last_u <- u[ok[1]]
    for (ix in ok) {
      a <- exp(-(u[ix]-last_u)/tau[j]);
      state <- a*state; P <- a*a*P+v*(1-a*a)
      F <- P+e[ix]^2
      if (is.finite(F) && F>0) {
        err <- y[ix]-mu[ix]-state
        innov[ix,j] <- err/sqrt(F)
        gain <- P/F
        state <- state+gain*err; P <- P*(1-gain)
      }
      last_u <- u[ix]
    }
  }
  R <- suppressWarnings(stats::cor(innov, use='pairwise.complete.obs'))
  if (any(!is.finite(R))) return(NULL)
  R <- (R+t(R))/2; diag(R) <- 1
  R <- (1-shrink)*R+shrink*diag(k)
  ee <- eigen(R, symmetric=TRUE)
  ee$values <- pmax(ee$values, 1e-4)
  R <- ee$vectors %*% diag(ee$values,k) %*% t(ee$vectors)
  stats::cov2cor(R)
}

drw <- function(data1, data2 = NULL, data3 = NULL, data4 = NULL, data5 = NULL,
                data6 = NULL, data7 = NULL, data8 = NULL, data9 = NULL, data10 = NULL,
                n.datasets, method = "mle", poly.order = 1,
                bayes.n.burn = 3000, bayes.n.sample = 1000,
                n.starts = 1, seed = NULL,
                optim.maxit = 3000, init.method = c("univariate", "legacy")) {

  run_started <- Sys.time()
  run_cpu_start <- proc.time()
  message("DRW fit started: ", format(run_started, "%Y-%m-%d %H:%M:%S %Z"))

  if (length(n.datasets) != 1 || !is.finite(n.datasets) ||
      n.datasets != as.integer(n.datasets) || n.datasets < 1 || n.datasets > 10) {
    stop("'n.datasets' must be an integer from 1 to 10.")
  }
  if (length(poly.order) != 1 || !is.finite(poly.order) ||
      poly.order != as.integer(poly.order) || poly.order < 0) {
    stop("'poly.order' must be a nonnegative integer.")
  }
  method <- match.arg(method, c("mle", "bayes"))
  init.method <- match.arg(init.method)
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

  if (length(n.starts) != 1L || !is.finite(n.starts) ||
      n.starts < 1 || n.starts != as.integer(n.starts))
    stop("'n.starts' must be a positive integer.")
  if (length(optim.maxit) != 1L || !is.finite(optim.maxit) ||
      optim.maxit < 1 || optim.maxit != as.integer(optim.maxit))
    stop("'optim.maxit' must be a positive integer.")
  if (!is.null(seed)) set.seed(seed)

  # Work in normalized time internally; report physical-time parameters.
  # For dX(t)=-X(t)/tau dt + sigma dW(t), normalized-time
  # diffusion variance = physical-time diffusion variance * time.range.
  y_cols <- seq(2, 2 * k, by = 2)
  e_cols <- seq(3, 2 * k + 1, by = 2)
  sd_y <- vapply(seq_len(k), function(j) {
    yy <- data.comb[, y_cols[j]]
    ee <- data.comb[, e_cols[j]]
    v <- stats::var(yy, na.rm = TRUE) - mean(ee^2, na.rm = TRUE)
    if (!is.finite(v) || v <= 1e-8) v <- stats::var(yy, na.rm = TRUE)
    sqrt(max(v, 1e-6, na.rm = TRUE))
  }, numeric(1))
  warm <- vector('list', k)
  if (init.method == 'univariate') {
    for (j in seq_len(k)) {
      sub <- data.comb[, c(1L, y_cols[j], e_cols[j]), drop=FALSE]
      warm[[j]] <- drw_univariate_warm(sub, raw_t_range, n_b_per_k,
                       NULL,
                       maxit = min(500L, as.integer(optim.maxit)))
    }
  }
  tau0 <- numeric(k); sig20 <- numeric(k)
  for (j in seq_len(k)) {
    if (!is.null(warm[[j]])) {
      tau0[j] <- warm[[j]]$tau
      sig20[j] <- warm[[j]]$sigma2
    } else {
      tj <- data.comb[,1][is.finite(data.comb[,y_cols[j]])]
      dj <- diff(sort(unique(tj))); dj <- dj[dj > 0]
      fallback <- if (length(dj)) sqrt(stats::median(dj) * (max(tj)-min(tj))) else .1 * raw_t_range
      if (init.method == 'legacy') fallback <- 100 * raw_t_range
      tau0[j] <- fallback / raw_t_range
      sig20[j] <- 2 * sd_y[j]^2 / tau0[j]
    }
  }
  n.cov <- 2L * k + n.rho
  lower_bounds <- c(rep(-25, k), rep(log(1e-5), k), rep(-5, n.rho))
  upper_bounds <- c(rep(25, k), rep(log(1e4), k), rep(5, n.rho))

  objective <- function(th) {
    sigma2 <- exp(th[seq_len(k)])
    tau <- exp(th[k + seq_len(k)])
    rho_values <- drw_corr_from_z(th[2L * k + seq_len(n.rho)], k)
    suff <- drw_filter_suff(data.comb, sigma2, tau, rho_values, n_b_per_k)
    prof <- drw_profile_from_suff(suff)
    if (!is.finite(prof$loglik)) return(1e12)
    -prof$loglik
  }
  # First start is deterministic, even when n.starts=1.
  z0 <- if (k > 1L && init.method == 'univariate') {
    drw_z_from_corr(matrix(.5, k, k) + diag(.5, k))
  } else rep(0, n.rho)
  theta0 <- c(log(sig20), log(tau0), z0)
  theta0 <- pmin(upper_bounds, pmax(lower_bounds, theta0))
  all_starts <- vector('list', as.integer(n.starts))
  all_starts[[1L]] <- theta0
  if (n.starts >= 2L) all_starts[[2L]] <- c(theta0[seq_len(2*k)], rep(0, n.rho))
  if (n.starts >= 3L) {
    base_suff <- drw_filter_suff(data.comb, exp(theta0[seq_len(k)]),
      exp(theta0[k+seq_len(k)]), drw_corr_from_z(theta0[2*k+seq_len(n.rho)],k),
      n_b_per_k)
    base_prof <- drw_profile_from_suff(base_suff)
    Ri <- if (is.finite(base_prof$loglik)) drw_innovation_corr_start(
      data.comb, exp(theta0[k+seq_len(k)]), exp(theta0[seq_len(k)]),
      base_prof$beta, k, n_b_per_k) else NULL
    all_starts[[3L]] <- c(theta0[seq_len(2*k)],
      if (is.null(Ri)) stats::runif(n.rho, -.4, .4) else drw_z_from_corr(Ri))
  }
  if (n.starts >= 4L) for (ii in 4:as.integer(n.starts)) {
    if (ii == 4L) {
      tt <- theta0 + c(rnorm(k, 0, .4), rnorm(k, 0, .7),
                       stats::runif(n.rho, -.7, .7) - z0)
    } else {
      tau_random <- vapply(seq_len(k), function(j) {
        if (!is.null(warm[[j]])) {
          exp(stats::runif(1, log(max(warm[[j]]$cadence, 1e-6)),
                                  log(max(warm[[j]]$baseline, warm[[j]]$cadence*1.01)))) / raw_t_range
        } else exp(stats::runif(1, log(1e-4), log(1)))
      }, numeric(1))
      tt <- c(log(2*sd_y^2/tau_random), log(tau_random),
              stats::runif(n.rho, -.7, .7))
    }
    all_starts[[ii]] <- pmin(upper_bounds, pmax(lower_bounds, tt))
  }
  if (method == "mle") {
  start_timings <- vector("list", length(all_starts))
  fits <- lapply(seq_along(all_starts), function(ii) {
    start <- all_starts[[ii]]
    t0 <- Sys.time(); c0 <- proc.time()
    message(sprintf("[%d/%d] Started: %s", ii, length(all_starts),
                    format(t0, "%Y-%m-%d %H:%M:%S %Z")))
    fit <- tryCatch(stats::optim(start, objective, method = "L-BFGS-B",
      lower = lower_bounds, upper = upper_bounds,
      control = list(maxit = optim.maxit, factr = 1e7)),
      error = function(e) list(value = Inf, convergence = 999L,
                              message = conditionMessage(e)))
    t1 <- Sys.time(); dc <- proc.time() - c0
    start_timings[[ii]] <<- data.frame(
      start = ii, started = as.character(t0), finished = as.character(t1),
      elapsed_seconds = as.numeric(difftime(t1, t0, units = "secs")),
      cpu_user_seconds = unname(dc[["user.self"]]),
      cpu_system_seconds = unname(dc[["sys.self"]]),
      cpu_seconds = unname(dc[["user.self"]] + dc[["sys.self"]]),
      child_cpu_seconds = unname(dc[["user.child"]] + dc[["sys.child"]]),
      negative_log_likelihood = fit$value,
      convergence = as.integer(fit$convergence), stringsAsFactors = FALSE)
    message(sprintf("[%d/%d] Finished: %s | %.2f min | logLik=%.6f | conv=%d",
                    ii, length(all_starts), format(t1, "%Y-%m-%d %H:%M:%S %Z"),
                    start_timings[[ii]]$elapsed_seconds / 60, -fit$value,
                    fit$convergence))
    fit
  })
  vals <- vapply(fits, function(f) f$value, numeric(1))
  if (!any(is.finite(vals))) stop("All MLE starts failed.")
  best <- which.min(vals)
  refine_started <- Sys.time(); refine_cpu_start <- proc.time()
  message("Final refinement started: ", format(refine_started, "%Y-%m-%d %H:%M:%S %Z"))
  opt.temp <- stats::optim(fits[[best]]$par, objective, method = "L-BFGS-B",
    lower = lower_bounds, upper = upper_bounds,
    control = list(maxit = optim.maxit, factr = 1e5))
  refine_finished <- Sys.time(); refine_cpu <- proc.time() - refine_cpu_start
  message(sprintf("Final refinement finished: %s | %.2f min | logLik=%.6f | conv=%d",
                  format(refine_finished, "%Y-%m-%d %H:%M:%S %Z"),
                  as.numeric(difftime(refine_finished, refine_started, units="mins")),
                  -opt.temp$value, opt.temp$convergence))
  sigma2.mle <- exp(opt.temp$par[seq_len(k)])
  tau.mle <- exp(opt.temp$par[k + seq_len(k)])
  rho.mle <- drw_corr_from_z(opt.temp$par[2L * k + seq_len(n.rho)], k)
  mle_suff <- drw_filter_suff(data.comb, sigma2.mle, tau.mle, rho.mle, n_b_per_k)
  mle_profile <- drw_profile_from_suff(mle_suff)
  if (!is.finite(mle_profile$loglik)) stop("Final likelihood is invalid.")
  initial.mle <- list(beta = mle_profile$beta,
                      sigma2 = as.numeric(sigma2.mle),
                      tau = as.numeric(tau.mle), rho = as.numeric(rho.mle))

  } # end joint MLE optimization
  if (method == "bayes") {
    # Bayesian sampling uses the univariate warm start directly, without
    # requiring joint MLE optimization; n.starts controls MLE only.
    warm_sigma2 <- exp(theta0[seq_len(k)])
    warm_tau <- exp(theta0[k + seq_len(k)])
    warm_rho <- drw_corr_from_z(theta0[2*k + seq_len(n.rho)], k)
    warm_suff <- drw_filter_suff(data.comb, warm_sigma2, warm_tau,
                                 warm_rho, n_b_per_k)
    warm_profile <- drw_profile_from_suff(warm_suff)
    if (!is.finite(warm_profile$loglik)) stop('Invalid Bayesian warm start.')
    initial.mle <- list(beta=warm_profile$beta, sigma2=warm_sigma2,
                        tau=warm_tau, rho=warm_rho)
    # The existing sampler operates in normalized time. Convert only at output.
    res <- bayes(data = data.comb, theta = initial.mle,
      n.warm = bayes.n.burn, n.sample = bayes.n.sample,
      k = k, n_b_per_k = n_b_per_k,
      lower_bounds = lower_bounds, upper_bounds = upper_bounds)
    res$tau <- res$tau * raw_t_range
    res$sigma <- sqrt(res$sigma2 / raw_t_range)
    res$sigma2 <- NULL
  } else {
    res <- initial.mle
    res$tau <- res$tau * raw_t_range
    res$sigma <- sqrt(res$sigma2 / raw_t_range)
    res$sigma2 <- NULL
    res$logLik <- mle_profile$loglik
    res$convergence <- opt.temp$convergence
    res$message <- opt.temp$message
    res$counts <- opt.temp$counts
    res$starts <- data.frame(start = seq_along(fits),
      negative_log_likelihood = vals,
      convergence = vapply(fits, function(f) f$convergence, integer(1)))
    res$best.start <- best
    res$timing.starts <- do.call(rbind, start_timings)
    res$timing.refinement <- list(
      started = refine_started, finished = refine_finished,
      elapsed_seconds = as.numeric(difftime(refine_finished, refine_started, units="secs")),
      cpu_seconds = unname(refine_cpu[["user.self"]] + refine_cpu[["sys.self"]]))
  }
  # Expose warm-start diagnostics in observation-time units. Keep internal
  # normalized warm starts untouched because the optimizer uses them.
  warm_report <- lapply(warm, function(w) {
    if (is.null(w)) return(NULL)
    w$tau <- w$tau * raw_t_range
    w$sigma2 <- w$sigma2 / raw_t_range
    w$sigma <- sqrt(w$sigma2)
    w
  })
  res$initialization <- list(method=init.method,
    n.starts=if (method=='mle') as.integer(n.starts) else 0L,
    univariate=warm_report, correlation='Cholesky partial correlations')
  run_finished <- Sys.time(); run_cpu <- proc.time() - run_cpu_start
  res$timing <- list(started = run_started, finished = run_finished,
    elapsed_seconds = as.numeric(difftime(run_finished, run_started, units="secs")),
    elapsed_minutes = as.numeric(difftime(run_finished, run_started, units="mins")),
    cpu_user_seconds = unname(run_cpu[["user.self"]]),
    cpu_system_seconds = unname(run_cpu[["sys.self"]]),
    cpu_seconds = unname(run_cpu[["user.self"]] + run_cpu[["sys.self"]]),
    child_cpu_seconds = unname(run_cpu[["user.child"]] + run_cpu[["sys.child"]]),
    starts = if (method == 'mle') res$timing.starts else NULL,
    refinement = if (method == 'mle') res$timing.refinement else NULL)
  if (method == 'mle') {
    res$timing.starts <- NULL
    res$timing.refinement <- NULL
  }
  message(sprintf("DRW fit finished: %s | total wall %.2f min | CPU %.2f min",
                  format(run_finished, "%Y-%m-%d %H:%M:%S %Z"),
                  res$timing$elapsed_minutes, res$timing$cpu_seconds / 60))
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
