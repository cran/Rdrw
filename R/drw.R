
log.lik <- function(data, theta) {
  
  # theta: mu, sigma, tau, each is a vector of size k, rho is a vector of size k(k-1)/2
 
  mu <- theta[[1]]
  k <- length(mu)
  sigma2 <- theta[[2]]
  tau <- theta[[3]]
  rho <- matrix(1, nrow = k, ncol = k)  
  rho[upper.tri(rho)] <- theta[[4]]
  rho[lower.tri(rho)] <- t(rho)[lower.tri(rho)]

  if (det(rho) <= 0) {

    -Inf

  } else {

    time.comb <- data[, 1]
    lc.comb <- data[, seq(2, 2 * k, by = 2)]
    var.lc.comb  <- data[, seq(3, 2 * k + 1, by = 2)]^2
    leng.time = length(time.comb) # n
  
    Sigma <- list() # T: k * k, sigma t|t-1
    Sigma.star <- list() # T: k * k, sigma t|t
    Sigma[[1]] <- t(rho * sqrt(sigma2)) * sqrt(sigma2)  
    
    temp <- matrix(0, k, k)
    for(i in 1 : k) {
      for(j in 1 : k) {
        temp[i, j] = 1 / tau[i] + 1 / tau[j]
      }
    }
    Sigma[[1]]  =  Sigma[[1]] / temp # Q

    mu.i <- matrix(0, leng.time, k) # n * K, mu t|t-1
    mu.star.i <- matrix(0, leng.time, k) # mu t|t
    mu.i[1, ] <- mu

    delta.t <- diff(time.comb)
    a.i <- exp(-delta.t %*% t(1 / tau)) # (n - 1) * k
  
    loglik <- 0

    for (t in 1 : leng.time) {

      if (t > 1) {
        Sigma[[t]] <-  t(a.i[t - 1, ] * Sigma.star[[t - 1]]) * a.i[t - 1, ] + 
                       Sigma[[1]] * (1 - exp(-temp * delta.t[t - 1]))
      }

      q <-  which(!is.na(lc.comb[t, ]))
      lc.t = lc.comb[t, q]
      var.t <- var.lc.comb[t, q]
    
      if (length(q) > 1) {
        Qt <- Sigma[[t]][q, q] + diag(var.t)
        invQt <- chol2inv(chol(Qt))
        Sigma.star[[t]] <- Sigma[[t]] - Sigma[[t]][, q] %*% invQt %*% Sigma[[t]][q, ]
      } else {
        Qt <- Sigma[[t]][q, q] + var.t
        invQt <- 1 / Qt
        Sigma.star[[t]] <- Sigma[[t]] - Sigma[[t]][, q] %*% t(Sigma[[t]][q, ]) * invQt 
      }
    
      if (t > 1) {
        mu.i[t, ] <- mu + a.i[t - 1, ] * (mu.star.i[t - 1, ] - mu)
      }

      if (length(q) > 1) {
        mu.star.i[t, ] <- mu.i[t, ] + Sigma[[t]][, q] %*% invQt %*% t(lc.t - mu.i[t, q])
      } else {
        mu.star.i[t, ] <- mu.i[t, ] + Sigma[[t]][, q] * (lc.t - mu.i[t, q]) * invQt
      }
    
      if(length(q) > 1) {
        loglik <- loglik +  dmvnorm(lc.t, mean = mu.i[t, q], sigma = Qt, log = TRUE)
      } else {
        loglik <- loglik +  dnorm(lc.t, mean = mu.i[t, q], sd = sqrt(Qt), log = TRUE)
      }
    }  
  
    as.numeric(loglik)

  }

}



bayes <- function (data, theta, n.warm, n.sample, 
                   mu.prop.scale, rho.prop.scale,
                   log.sigma2.prop.scale, log.tau.prop.scale,
                   mu.prior.range,
                   tau.prior.a, tau.prior.b, 
                   sigma.prior.a, sigma.prior.b) {
  
  n.total <- n.sample + n.warm
  theta.t <- theta
  k <- length(theta[[1]])
  mu.accept <- matrix(0, nrow = n.total, ncol = k)
  sigma2.accept <- matrix(0, nrow = n.total, ncol = k)
  tau.accept <- matrix(0, nrow = n.total, ncol = k)
  rho.accept <- matrix(0, nrow = n.total, ncol = k * (k - 1) / 2)

  mu.out <- matrix(NA, nrow = n.total, ncol = k)
  sigma2.out <- matrix(NA, nrow = n.total, ncol = k)
  tau.out <- matrix(NA, nrow = n.total, ncol = k)
  rho.out <- matrix(NA, nrow = n.total, ncol = k * (k - 1) / 2)

  for (i in 1 : n.total) {

    # updating mu
    for (j in 1 : k) {
      mu.t <- theta.t[[1]][j]
      inv.cdf <- runif(1, min = pnorm(mu.prior.range[1], mean = mu.t, sd = mu.prop.scale[j]), 
                          max = pnorm(mu.prior.range[2], mean = mu.t, sd = mu.prop.scale[j]))
      mu.p <- qnorm(inv.cdf, mean = mu.t, sd = mu.prop.scale[j])

      theta.p <- theta.t
      theta.p[[1]][j] <- mu.p
      l.metrop <- log.lik(data, theta.p) - log.lik(data, theta.t) 
      l.hastings <- -log(pnorm((mu.prior.range[2] - mu.p) / mu.prop.scale[j]) - 
                         pnorm((mu.prior.range[1]- mu.p) / mu.prop.scale[j])) +
                    log(pnorm((mu.prior.range[2] - mu.t) / mu.prop.scale[j]) - 
                        pnorm((mu.prior.range[1] - mu.t) / mu.prop.scale[j]))
      # Accept-reject
      if (l.metrop + l.hastings > -rexp(1)) {
        theta.t[[1]][j] <- mu.p
        mu.accept[i, j] <- 1
      }
      mu.out[i, j] <- theta.t[[1]][j]

      if (i %% 100 == 0) {
        if(mean(mu.accept[(i - 99) : i, j]) > 0.35) {
          scale.adj <- exp(min(0.1, 1 / sqrt(i / 100)))
        } else if (mean(mu.accept[(i - 99) : i, j]) < 0.35) {
          scale.adj <- exp(-min(0.1, 1 / sqrt(i / 100)))
        }
        mu.prop.scale[j] <- mu.prop.scale[j] * scale.adj
      }
    }

    # updating sigma2

    for (j in 1 : k) {
      sigma2.t <-  theta.t[[2]][j]
      sigma2.p <- exp(rnorm(1, mean = log(sigma2.t), sd = log.sigma2.prop.scale[j]))
      theta.p <- theta.t
      theta.p[[2]][j] <- sigma2.p
      l.metrop <- log.lik(data, theta.p) - log.lik(data, theta.t) 
      l.metrop <- l.metrop - sigma.prior.b / sigma2.p - (sigma.prior.a + 1) * log(sigma2.p) + 
                             sigma.prior.b / sigma2.t + (sigma.prior.a + 1) * log(sigma2.t)
      l.hastings <- log(sigma2.p) - log(sigma2.t)

      # Accept-reject
      if (l.metrop + l.hastings > -rexp(1)) {
        theta.t[[2]][j] <- sigma2.p
       sigma2.accept[i, j] <- 1
      }
      sigma2.out[i, j] <- theta.t[[2]][j]

      if (i %% 100 == 0) {
        if(mean(sigma2.accept[(i - 99) : i, j]) > 0.35) {
          scale.adj <- exp(min(0.1, 1 / sqrt(i / 100)))
        } else if (mean(sigma2.accept[(i - 99) : i, j]) < 0.35) {
          scale.adj <- exp(-min(0.1, 1 / sqrt(i / 100)))
        }
        log.sigma2.prop.scale[j] <- log.sigma2.prop.scale[j] * scale.adj
      }
    }

    # updating tau
    for (j in 1 : k) {
      tau.t <-  theta.t[[3]][j]
      tau.p <- exp(rnorm(1, mean = log(tau.t), sd = log.tau.prop.scale[j]))
      theta.p <- theta.t
      theta.p[[3]][j] = tau.p
      l.metrop <- log.lik(data, theta.p) - log.lik(data, theta.t) 
      l.metrop <- l.metrop - tau.prior.b / tau.p - (tau.prior.a + 1) * log(tau.p) + 
                             tau.prior.b / tau.t + (tau.prior.a + 1) * log(tau.t)
      l.hastings <- log(tau.p) - log(tau.t)

      # Accept-reject
      if (l.metrop + l.hastings > -rexp(1)) {
        theta.t[[3]][j] <- tau.p
        tau.accept[i, j] <- 1
      }
      tau.out[i, j] <- theta.t[[3]][j]

      if (i %% 100 == 0) {
        if(mean(tau.accept[(i - 99) : i, j]) > 0.35) {
          scale.adj <- exp(min(0.1, 1 / sqrt(i / 100)))
        } else if (mean(tau.accept[(i - 99) : i, j]) < 0.35) {
         scale.adj <- exp(-min(0.1, 1 / sqrt(i / 100)))
        }
        log.tau.prop.scale[j] <- log.tau.prop.scale[j] * scale.adj
      }
    }

    # updating rho
    for (j in 1 : (k * (k - 1) / 2)) {
      rho.t <-  theta.t[[4]][j]
      inv.cdf <- runif(1, min = pnorm(-1, mean = rho.t, sd = rho.prop.scale[j]), 
                          max = pnorm(1, mean = rho.t, sd = rho.prop.scale[j]))
      rho.p <- qnorm(inv.cdf, mean = rho.t, sd = rho.prop.scale[j])
      theta.p <- theta.t
      theta.p[[4]][j] <- rho.p
      l.metrop <- log.lik(data, theta.p) - log.lik(data, theta.t) 
      l.hastings <- -log(pnorm((1 - rho.p) / rho.prop.scale[j]) - pnorm((-1 - rho.p) / rho.prop.scale[j])) +
                    log(pnorm((1 - rho.t) / rho.prop.scale[j]) - pnorm((-1 - rho.t) / rho.prop.scale[j]))
      # Accept-reject
      if (l.metrop + l.hastings > -rexp(1)) {
        theta.t[[4]][j] <- rho.p
        rho.accept[i, j] <- 1
      }
      rho.out[i, j] <- theta.t[[4]][j]

      if (i %% 100 == 0) {
        if(mean(rho.accept[(i - 99) : i, j]) > 0.35) {
          scale.adj <- exp(min(0.1, 1 / sqrt(i / 100)))
        } else if (mean(rho.accept[(i - 99) : i, j]) < 0.35) {
          scale.adj <- exp(-min(0.1, 1 / sqrt(i / 100)))
        }
        rho.prop.scale[j] <- rho.prop.scale[j] * scale.adj
      }
    }

  }

  mu.acct <- colMeans(mu.accept)
  sigma2.acct <- colMeans(sigma2.accept)
  tau.acct <- colMeans(tau.accept)
  rho.acct <- colMeans(rho.accept)

  out <- list(mu = mu.out[-c(1 : n.warm), ], sigma = sqrt(sigma2.out[-c(1 : n.warm), ]), 
              tau = tau.out[-c(1 : n.warm), ],  rho = rho.out[-c(1 : n.warm), ], 
              mu.accept.rate = mu.acct, sigma.accept.rate = sigma2.acct, 
              tau.accept.rate = tau.acct, rho.accept.rate = rho.acct)
  out

}



log.lik.single <- function(data, theta) {
  
  # theta: mu, sigma, tau, each is a vector of size k, rho is a vector of size k(k-1)/2
 
  mu <- theta[[1]]
  k <- length(mu)
  sigma2 <- theta[[2]]
  tau <- theta[[3]]

  time.comb <- data[, 1]
  lc.comb <- data[, seq(2, 2 * k, by = 2)]
  var.lc.comb  <- data[, seq(3, 2 * k + 1, by = 2)]^2
  leng.time = length(time.comb) # n
  
  Sigma <- list() # T: k * k, sigma t|t-1
  Sigma.star <- list() # T: k * k, sigma t|t
  Sigma[[1]] <- sigma2 * tau / 2
    
  mu.i <- rep(0, leng.time) # n * K, mu t|t-1
  mu.star.i <- rep(0, leng.time) # mu t|t
  mu.i[1] <- mu

    delta.t <- diff(time.comb)
    a.i <- exp(-delta.t / tau)
  
    loglik <- 0

    for (t in 1 : leng.time) {

      if (t > 1) {
        Sigma[[t]] <-  t(a.i[t - 1] * Sigma.star[[t - 1]]) * a.i[t - 1] + Sigma[[1]] * (1 - exp(-delta.t[t - 1] * 2 / tau))
      }

      lc.t = lc.comb[t]
      var.t <- var.lc.comb[t]
        Qt <- Sigma[[t]] + var.t
        invQt <- 1 / Qt
        Sigma.star[[t]] <- Sigma[[t]] - Sigma[[t]] * Sigma[[t]] * invQt 
    
      if (t > 1) {
        mu.i[t] <- mu + a.i[t - 1] * (mu.star.i[t - 1] - mu)
      }

        mu.star.i[t] <- mu.i[t] + Sigma[[t]] * (lc.t - mu.i[t]) * invQt
    
        loglik <- loglik +  dnorm(lc.t, mean = mu.i[t], sd = sqrt(Qt), log = TRUE)
    }  
  
    as.numeric(loglik)

  }



bayes.single <- function (data, theta, n.warm, n.sample,
                          mu.prop.scale, log.sigma2.prop.scale, log.tau.prop.scale,
                          mu.prior.range, tau.prior.a, tau.prior.b, sigma.prior.a, sigma.prior.b) {
  
  n.total <- n.sample + n.warm
  theta.t <- theta
  k <- length(theta[[1]])
  mu.accept <- matrix(0, nrow = n.total, ncol = k)
  sigma2.accept <- rep(0, n.total)
  tau.accept <- rep(0, n.total)

  mu.out <- matrix(NA, nrow = n.total, ncol = k)
  sigma2.out <- rep(NA, n.total)
  tau.out <- rep(NA, n.total)

  for (i in 1 : n.total) {

    # updating mu
    for (j in 1 : k) {
      mu.t <- theta.t[[1]][j]
      inv.cdf <- runif(1, min = pnorm(mu.prior.range[1], mean = mu.t, sd = mu.prop.scale[j]), 
                          max = pnorm(mu.prior.range[2], mean = mu.t, sd = mu.prop.scale[j]))
      mu.p <- qnorm(inv.cdf, mean = mu.t, sd = mu.prop.scale[j])

      theta.p <- theta.t
      theta.p[[1]][j] <- mu.p
      l.metrop <- log.lik.single(data, theta.p) - log.lik.single(data, theta.t) 
      l.hastings <- -log(pnorm((mu.prior.range[2] - mu.p) / mu.prop.scale[j]) - 
                         pnorm((mu.prior.range[1] - mu.p) / mu.prop.scale[j])) +
                    log(pnorm((mu.prior.range[2] - mu.t) / mu.prop.scale[j]) - 
                        pnorm((mu.prior.range[1] - mu.t) / mu.prop.scale[j]))
      # Accept-reject
      if (l.metrop + l.hastings > -rexp(1)) {
        theta.t[[1]][j] <- mu.p
        mu.accept[i, j] <- 1
      }
      mu.out[i, j] <- theta.t[[1]][j]

      if (i %% 100 == 0) {
        if(mean(mu.accept[(i - 99) : i, j]) > 0.35) {
          scale.adj <- exp(min(0.1, 1 / sqrt(i / 100)))
        } else if (mean(mu.accept[(i - 99) : i, j]) < 0.35) {
          scale.adj <- exp(-min(0.1, 1 / sqrt(i / 100)))
        }
        mu.prop.scale[j] <- mu.prop.scale[j] * scale.adj
      }
    }

    # updating sigma2
    sigma2.t <-  theta.t[[2]]
    sigma2.p <- exp(rnorm(1, mean = log(sigma2.t), sd = log.sigma2.prop.scale))
    theta.p <- theta.t
    theta.p[[2]] = sigma2.p
    l.metrop <- log.lik.single(data, theta.p) - log.lik.single(data, theta.t) 
    l.metrop <- l.metrop - sigma.prior.b / sigma2.p - (sigma.prior.a + 1) * log(sigma2.p) + 
                           sigma.prior.b / sigma2.t + (sigma.prior.a + 1) * log(sigma2.t)
    l.hastings <- log(sigma2.p) - log(sigma2.t)

    # Accept-reject
    if (l.metrop + l.hastings > -rexp(1)) {
      theta.t[[2]] <- sigma2.p
      sigma2.accept[i] <- 1
    }
    sigma2.out[i] <- theta.t[[2]]

    if (i %% 100 == 0) {
      if(mean(sigma2.accept[(i - 99) : i]) > 0.35) {
        scale.adj <- exp(min(0.1, 1 / sqrt(i / 100)))
      } else if (mean(sigma2.accept[(i - 99) : i]) < 0.35) {
        scale.adj <- exp(-min(0.1, 1 / sqrt(i / 100)))
      }
      log.sigma2.prop.scale <- log.sigma2.prop.scale * scale.adj
    }

    # updating tau
    tau.t <-  theta.t[[3]]
    tau.p <- exp(rnorm(1, mean = log(tau.t), sd = log.tau.prop.scale))
    theta.p <- theta.t
    theta.p[[3]] = tau.p
    l.metrop <- log.lik.single(data, theta.p) - log.lik.single(data, theta.t) 
    l.metrop <- l.metrop - tau.prior.b / tau.p - (tau.prior.a + 1) * log(tau.p) + 
                           tau.prior.b / tau.t + (tau.prior.a + 1) * log(tau.t)
    l.hastings <- log(tau.p) - log(tau.t)

    # Accept-reject
    if (l.metrop + l.hastings > -rexp(1)) {
      theta.t[[3]] <- tau.p
      tau.accept[i] <- 1
    }
    tau.out[i] <- theta.t[[3]]

    if (i %% 100 == 0) {
      if(mean(tau.accept[(i - 99) : i]) > 0.35) {
        scale.adj <- exp(min(0.1, 1 / sqrt(i / 100)))
      } else if (mean(tau.accept[(i - 99) : i]) < 0.35) {
        scale.adj <- exp(-min(0.1, 1 / sqrt(i / 100)))
      }
      log.tau.prop.scale <- log.tau.prop.scale * scale.adj
    }

    # updating rho

  }

  mu.acct <- colMeans(mu.accept)
  sigma2.acct <- mean(sigma2.accept)
  tau.acct <- mean(tau.accept)

  out <- list(mu = mu.out[-c(1 : n.warm), ], sigma = sqrt(sigma2.out[-c(1 : n.warm)]), 
              tau = tau.out[-c(1 : n.warm)], 
              mu.accept.rate = mu.acct, sigma.accept.rate = sigma2.acct, 
              tau.accept.rate = tau.acct)
  out

}



drw <- function(data1, data2, data3, data4, data5, 
                data6, data7, data8, data9, data10,
                n.datasets, method = "mle",
                bayes.n.burn, bayes.n.sample,
                mu.UNIFprior.range = c(-30, 30),
                tau.IGprior.shape = 1, tau.IGprior.scale = 1,
                sigma2.IGprior.shape = 1, sigma2.IGprior.scale = 1e-7) {

  message(paste("Starting at: ", Sys.time()))
  k <- n.datasets
  n.rho <- k * (k - 1) / 2

  if (k == 1) {

    log.lik.single.optim <- function(th, data) {
      mu <- th[1]
      sigma2 <- exp(th[2])
      tau <- exp(th[3])
      log.lik.single(data, list(mu, sigma2, tau))
    }

    initial <- c(mean(data1[, 2]), 2 * log(mean(data1[, 3])), log(100))
    opt.temp <- optim(initial, log.lik.single.optim, control = list(fnscale = -1), 
                      hessian = FALSE, method = "Nelder-Mead", data = data1)
    initial.mle <- list(mu = as.numeric(opt.temp$par[1]), 
                        sigma2 = as.numeric(exp(opt.temp$par[(k + 1)])), 
                        tau = as.numeric(exp(opt.temp$par[(k + 2)])))
    temp <- initial.mle
    temp[[2]] <- sqrt(temp[[2]])
    res <- temp
    names(res)[2] <- "sigma"

    if (method == "bayes") {
      res <- bayes.single(data = data1, theta = initial.mle, 
             n.warm = bayes.n.burn, n.sample = bayes.n.sample,
             mu.prop.scale = 0.05, 
             log.sigma2.prop.scale = 0.05,
             log.tau.prop.scale = 1,
             mu.prior.range <- mu.UNIFprior.range,
             tau.prior.a = tau.IGprior.shape, tau.prior.b = tau.IGprior.scale,
             sigma.prior.a = sigma2.IGprior.shape, sigma.prior.b = sigma2.IGprior.scale)
      res[[7]] <- data1
      names(res)[7] <- "data.comb"
    }    

  } else {

    dat <- vector(mode = "list", length = k)
    for (i in 1 : k) {
      eval(parse(text = paste0("data.temp <- data", i)))
      colnames(data.temp)[1] <- "V1"
      dat[[i]] <- data.temp
    }

    data.comb <- NULL

    for (data in dat) {
      if (is.null(data.comb)) {
        data.comb <- data
      } else {
        data.comb <- merge(data.comb, data, by.x = "V1", by.y = "V1", all = TRUE)
      }  
    }

    log.lik.optim <- function(th, k, data) {
      n.rho <- k * (k - 1) / 2
      mu <- th[1 : k]
      sigma2 <- exp(th[(k + 1) : (2 * k)])
      tau <- exp(th[(2 * k + 1) : (3 * k)])
      rho <- 2 * exp(th[(3 * k + 1) : (3 * k + n.rho)]) / 
                 (1 + exp(th[(3 * k + 1) : (3 * k + n.rho)])) - 1
      log.lik(data, list(mu, sigma2, tau, rho))
    }

    initial.temp <- c(colMeans(data.comb[, seq(2, 2 * k, by = 2)], na.rm = TRUE), 
                      2 * log(colMeans(data.comb[seq(2, 2 * k, by = 2) + 1], na.rm = TRUE)),
                      log(rep(100, k)), 
                      rep(0, k * (k - 1) / 2))
    opt.temp <- optim(initial.temp, log.lik.optim, control = list(fnscale = -1), 
                      hessian = FALSE, method = "Nelder-Mead", k = k, data = data.comb)
    initial.mle <- list(mu = as.numeric(opt.temp$par[1 : k]), 
                        sigma2 = as.numeric(exp(opt.temp$par[(k + 1) : (2 * k)])), 
                        tau = as.numeric(exp(opt.temp$par[(2 * k + 1) : (3 * k)])), 
                        rho = as.numeric(2 * exp(opt.temp$par[(3 * k + 1) : (3 * k + n.rho)]) / 
                                (1 + exp(opt.temp$par[(3 * k + 1) : (3 * k + n.rho)])) - 1))
    temp <- initial.mle
    temp[[2]] <- sqrt(temp[[2]]) # make sigma from sigma2
    res <- temp
    names(res)[2] <- "sigma"

    if (method == "bayes") {
      res <- bayes(data = data.comb, theta = initial.mle, 
                   n.warm = bayes.n.burn, n.sample = bayes.n.sample,
                   mu.prop.scale = rep(0.05, k), 
                   log.sigma2.prop.scale = rep(0.05, k),
                   log.tau.prop.scale = rep(1, k),
                   rho.prop.scale = rep(0.1, n.rho),
                   mu.prior.range <- mu.UNIFprior.range,
                   tau.prior.a = tau.IGprior.shape, tau.prior.b = tau.IGprior.scale,
                   sigma.prior.a = sigma2.IGprior.shape, sigma.prior.b = sigma2.IGprior.scale)
      res[[9]] <- data.comb
      names(res)[9] <- "data.comb"
    }
  }

  message(paste("Ending at: ", Sys.time()))
  res
  
}



drw.sim <- function(time, n.datasets, measure.error.SD,
                    mu, sigma, tau, rho) {

  k <- n.datasets
  n <- length(time)

  if (k == 1){

    if (is.null(measure.error.SD)) {
      measure.error.SD <- rep(0, n)
    }

    delta.t <- diff(time)
    a.i <- exp( -delta.t / tau)

    X <- rep(NA, n)
    X[1] <- rnorm(1, mean = mu, sd = sigma * sqrt(tau / 2))
    for (i in 2 : n) {
      X[i] <- rnorm(1, mean = mu + a.i[i - 1] * (X[i - 1] - mu), 
                       sd = sigma * sqrt(tau * (1 - a.i[i - 1]^2) / 2))
    }
  
    x <- rnorm(n, mean = X, sd = measure.error.SD)

  } else {

    if (is.null(measure.error.SD)) {
      measure.error.SD <- matrix(0, nrow = n, ncol = k)
    }

    rho.mat <- matrix(1, nrow = k, ncol = k)  
    rho.mat[upper.tri(rho.mat)] <- rho
    rho.mat[lower.tri(rho.mat)] <- t(rho.mat)[lower.tri(rho.mat)]

    if (det(rho.mat) == 0) {
      warning("The resulting correlation matrix is singular.")
      quit()
    }

    delta.t <- diff(time)
    a.i <- exp(-delta.t %*% t(1 / tau)) # (n - 1) * k

    X <- matrix(NA, nrow = n, ncol = k)
  
    Q <- list() # T: k * k, sigma t|t-1
    Q[[1]] <- t(rho.mat * sigma) * sigma
    temp <- matrix(0, k, k)
    for(i in 1 : k) {
      for(j in 1 : k) {
        temp[i, j] = 1 / tau[i] + 1 / tau[j]
      }
    }
    Q[[1]]  <-  Q[[1]] / temp # Q

    M <- list()
    M[[1]] <- mu
    X[1, ] <- rmvnorm(1, mean = M[[1]], sigma = Q[[1]])

    for (i in 2 : n) {
      M[[i]] <- mu + a.i[i - 1, ] * (X[i - 1, ] - mu)
      Q[[i]] <- Q[[1]] * (1 - exp(-temp * delta.t[i - 1]))
      X[i, ] <- rmvnorm(1, mean = M[[i]], sigma = Q[[i]])
    }

    x <- matrix(rnorm(n * k, mean = X, sd = measure.error.SD), nrow = n, ncol = k)

  }

  x

}