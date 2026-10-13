\name{drw}
\alias{drw}
\title{Fitting Univariate and Multivariate Damped Random Walk Processes}
\usage{
drw(data1, data2 = NULL, data3 = NULL, data4 = NULL, data5 = NULL,
    data6 = NULL, data7 = NULL, data8 = NULL, data9 = NULL,
    data10 = NULL, n.datasets, method = "mle", poly.order = 1,
    bayes.n.burn = 3000, bayes.n.sample = 1000,
    n.starts = 1, seed = NULL, optim.maxit = 3000,
    init.method = c("univariate", "legacy"))
}
\arguments{
\item{data1}{An n_1 by 3 matrix or data frame for the first time series. The first column contains observation times, the second column contains measurements, and the third column contains measurement error standard deviations. If measurement error standard deviations are unavailable, use zeros in the third column.}
\item{data2}{Optional second data set in the same format as \code{data1}.}
\item{data3}{Optional third data set in the same format as \code{data1}.}
\item{data4}{Optional fourth data set in the same format as \code{data1}.}
\item{data5}{Optional fifth data set in the same format as \code{data1}.}
\item{data6}{Optional sixth data set in the same format as \code{data1}.}
\item{data7}{Optional seventh data set in the same format as \code{data1}.}
\item{data8}{Optional eighth data set in the same format as \code{data1}.}
\item{data9}{Optional ninth data set in the same format as \code{data1}.}
\item{data10}{Optional tenth data set in the same format as \code{data1}. The current version allows up to ten time series data sets.}
\item{n.datasets}{The number of time series data sets to be modeled jointly. This must be an integer from 1 to 10.}
\item{method}{Either \code{"mle"} for maximum likelihood estimation or \code{"bayes"} for posterior sampling. Maximum likelihood estimation is computationally efficient and suitable for large-scale data analysis, while Bayesian posterior sampling is better suited to small-scale analyses requiring more careful uncertainty quantification.}
\item{poly.order}{The order of the polynomial trend used for the mean function of each time series. The default is 1, corresponding to an intercept and a linear trend in normalized time. Use 0 for the constant-mean damped random walk model.}
\item{bayes.n.burn}{The number of warm-up iterations when \code{method = "bayes"}.}
\item{n.starts}{Number of joint MLE starting points (default 1). Univariate preliminary fits are computed separately and do not count toward this number.}
\item{seed}{Optional random seed for randomized MLE starts and Bayesian MCMC.}
\item{optim.maxit}{Maximum iterations for each joint MLE optimization and final refinement.}
\item{init.method}{\code{"univariate"} (default) obtains observation-adaptive univariate DRW maximum likelihood warm starts for each series; \code{"legacy"} skips these fits and uses the previous fixed normalized-timescale starting scheme. The latter does not reproduce all aspects of the original optimizer.}
\item{bayes.n.sample}{The number of posterior samples saved after warm-up when \code{method = "bayes"}.}
}
\value{
A named list. Time units refer to the original input observation-time units,
not the internal normalized time coordinate.

For \code{method = "mle"}, the returned components are:
\describe{
\item{beta}{Fitted polynomial mean coefficients, grouped by series and ordered
from degree 0 to \code{poly.order}. Polynomial time is normalized to the
combined observation interval [0, 1]; coefficients of degree 1 and higher
are not expressed per day.}
\item{sigma}{Fitted diffusion standard deviations, in measurement units divided
by the square root of the input time unit. Not stationary standard deviations;
stationary SD is \code{sigma * sqrt(tau / 2)}.}
\item{tau}{Fitted damping timescales in the original input time units.}
\item{rho}{Pairwise correlations of the driving Brownian motions, ordered as
lower-triangular pairs (2,1), (3,1), (3,2), etc.; empty for a single series.
These are not zero-lag correlations of the latent processes. The latter equal
\code{rho_ij * 2 * sqrt(tau_i * tau_j) / (tau_i + tau_j)}.}
\item{logLik}{Maximized joint log likelihood.}
\item{convergence}{Convergence code from the final \code{optim} refinement;
zero conventionally indicates successful optimizer termination.}
\item{message}{Optimizer's final convergence message, when provided.}
\item{counts}{Final optimizer function and gradient evaluation counts.}
\item{starts}{Data frame with each joint starting point, its negative log
likelihood and convergence code, before final refinement.}
\item{best.start}{Index of the lowest-objective preliminary joint start.
The final refinement can improve upon this start.}
\item{initialization}{List containing \code{method}, \code{n.starts},
\code{correlation}, and \code{univariate}. The latter is a list, one entry
per series, of preliminary univariate fit diagnostics, or \code{NULL} when
unavailable. Each successful entry contains \code{tau} (original time units),
\code{sigma2} (diffusion variance rate, measurement units squared per input
time unit), \code{sigma} (its square root), \code{convergence}, \code{logLik},
\code{cadence}, and \code{baseline} (both in original time units).
Preliminary estimates are used only as numerical initializations.}
\item{timing}{List with \code{started} and \code{finished} (local timestamp
with time-zone information stored as POSIXct), \code{elapsed_seconds},
\code{elapsed_minutes} (wall-clock duration), \code{cpu_user_seconds},
\code{cpu_system_seconds}, \code{cpu_seconds} (user plus system CPU consumed
by the main R process), \code{child_cpu_seconds} (child-process CPU, when
reported by the platform), \code{starts} (per-start timing data frame),
and \code{refinement} (final-refinement timing list). Per-start timing rows
include timestamps, wall and CPU seconds, negative log likelihood, and
convergence code. Total wall time includes data preparation, preliminary
univariate fitting, joint starts, refinement, and result assembly.
CPU time and wall time differ; child CPU is not included in
\code{cpu_seconds}.}
}
For \code{method = "bayes"}, \code{beta}, \code{sigma}, \code{tau}, and
\code{rho} are posterior draws, with one row per retained MCMC iteration.
The sampler also returns \code{sigma.accept.rate}, \code{tau.accept.rate},
and \code{rho.accept.rate}, describing Metropolis acceptance proportions.
The \code{initialization} and \code{timing} lists are also returned; for
Bayesian fits, \code{timing$starts} and \code{timing$refinement} are
\code{NULL}, because no joint multistart MLE is run. All timings are
measurements of the current call, not estimates of future runtime.
}
\description{
The function \code{drw} fits univariate and multivariate damped random walk processes to one or more irregularly spaced time series with possibly heteroscedastic measurement errors. The current implementation allows each time series to have a polynomial mean trend in normalized time. This feature is useful in applications such as stock price prediction, where a constant mean may be too restrictive. The likelihood is evaluated by Kalman filtering. Conditional on the damped random walk covariance parameters, the polynomial mean coefficients are linear Gaussian location parameters. For maximum likelihood estimation they are profiled analytically by generalized least squares within the Kalman recursion, and for Bayesian inference they are updated from their exact Gaussian conditional distribution. The function returns maximum likelihood estimates or posterior samples of the model parameters.
}
\details{
The multivariate damped random walk process is also known as the Ornstein--Uhlenbeck process or a CARMA(1, 0) process. In the updated model, the long-term mean of the j-th time series is represented as

m_j(u) = beta_j0 + beta_j1 * u + ... + beta_jp * u^p,

where p is \code{poly.order}. For the polynomial mean only, the time coordinate u is defined as,

u = (t - t_min)/(t_max - t_min),

where t_min and t_max are the minimum and maximum combined observation times, respectively. Setting \code{poly.order = 0} recovers the constant-mean specification in the original package.

The timescale \code{tau} is expressed in the same units as the supplied observation times. For example, with input times in days, \code{tau = 100} means 100 days. The diffusion standard deviation \code{sigma} has units of the observations divided by the square root of the observation time unit.

The polynomial coefficients in \code{beta} are expressed in this dimensionless polynomial basis (unlike \code{tau} and \code{sigma}). For example, with \code{poly.order = 1}, the fitted mean is beta_j0 + beta_j1 * u, so beta_j1 is the total linear change over the normalized interval [0, 1], not the daily slope.

For computational efficiency, the polynomial coefficients are not included in the nonlinear optimizer used for maximum likelihood estimation. At each proposed set of covariance parameters, the Kalman recursion accumulates the Gaussian sufficient statistics for the polynomial coefficients and solves for their conditional generalized least squares estimates exactly. The coefficients remain estimated model parameters and are returned in the same order as in previous versions.

For Bayesian inference, the same Kalman sufficient statistics define the exact Gaussian conditional distribution of the polynomial coefficients under the package's diffuse Gaussian prior. The sampler draws these coefficients directly and caches the current Kalman sufficient statistics and log likelihood during the Metropolis--Hastings updates of the covariance parameters, avoiding redundant likelihood evaluations.

\strong{Initialization and optimization.} By default, each marginal series is fitted as a univariate OU/DRW model before joint inference. Each preliminary fit uses three observation-adaptive timescale initializations spanning representative within-band cadence and observational baseline; initial diffusion variance is matched to the measurement-error-adjusted empirical stationary variance. The preliminary fits provide only starting values, not fixed parameters, likelihood penalties, or Bayesian priors. If a univariate fit is unavailable, a cadence/baseline-based fallback is used. 

For joint MLE, \code{n.starts = 1} uses the univariate warm starts and an equicorrelation matrix with all pairwise correlations equal to 0.5. With two or more starts, the second uses independence; the third, when requested, uses a shrunken correlation estimate of overlapping standardized marginal Kalman innovations (or a random fallback). Subsequent starts perturb the marginal fits and explore observation-adaptive random timescales and valid random correlation matrices. The innovation-based correlations are numerical initializations, not estimates of the driving-noise correlations. Correlations are parameterized using Cholesky partial correlations, guaranteeing positive definiteness. All starts optimize the original joint likelihood and the best solution is refined. \code{init.method = "legacy"} skips marginal fits and uses a fixed normalized-time initialization. \code{n.starts} controls joint MLE only.

For \code{method = "bayes"}, the same marginal warm starts and valid equicorrelation initialization seed the MCMC directly, without requiring a preliminary joint MLE. The correlation sampler uses bounded unconstrained Cholesky partial correlations, with a uniform prior on these transformed coordinates (not a uniform prior on the pairwise correlations). Symmetric random-walk proposals preserve the target posterior on this parameterization. Other covariance parameters retain bounded uniform priors on their logarithmic coordinates, and the polynomial mean coefficients retain a diffuse Gaussian prior. Data-informed initial states do not enter the posterior prior or likelihood. Multiple chains and convergence checks are recommended.

The result omits the merged data matrix; marginal warm-start diagnostics are in \code{initialization}. Both the final estimates and the reported preliminary timescales use the original observation time units. Progress messages report each joint MLE start and its completion, followed by final refinement and total elapsed wall and CPU times. The diffusion standard deviation \code{sigma} is distinct from the stationary standard deviation: the latter equals \code{sigma * sqrt(tau / 2)}.

For multivariate fitting, the individual data sets are merged by observation time. Missing measurements at a given time are allowed and are handled by the Kalman filter. The input measurement-error column should contain standard deviations, not variances.

When astronomical time series data are loaded into R by \code{read.table}, \code{read.csv}, or related functions, decimal places of observation times may be rounded because of R's display and input defaults. If high time precision is needed, consider setting \code{options(digits = 11)} before loading the data.
}
\examples{
set.seed(1)
n1 <- 20
obs.time1 <- cumsum(rgamma(n1, shape = 3, rate = 1))
y1 <- rnorm(n1)
measure.error.SD1 <- rgamma(n1, shape = 0.01)
data1 <- cbind(obs.time1, y1, measure.error.SD1)

res1.mle <- drw(data1 = data1, n.datasets = 1, method = "mle", poly.order = 1)
names(res1.mle)
res1.mle$beta
res1.mle$sigma
res1.mle$tau

\donttest{
res1.bayes <- drw(data1 = data1, n.datasets = 1, method = "bayes",
                  poly.order = 1, bayes.n.burn = 10, bayes.n.sample = 10)
}

n2 <- 15
obs.time2 <- cumsum(rgamma(n2, shape = 3, rate = 1))
y2 <- rnorm(n2)
measure.error.SD2 <- rgamma(n2, shape = 0.01)
data2 <- cbind(obs.time2, y2, measure.error.SD2)

\donttest{
res2.mle <- drw(data1 = data1, data2 = data2, n.datasets = 2,
                method = "mle", poly.order = 1, n.starts = 5)
}
}
\author{Zhirui Hu and Hyungsuk Tak}
\references{Zhirui Hu and Hyungsuk Tak (2020), "Modeling Stochastic Variability in Multi-Band Time Series Data," doi:10.3847/1538-3881/abc1e2.}
