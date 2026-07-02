\name{drw}
\alias{drw}
\title{Fitting Univariate and Multivariate Damped Random Walk Processes}
\usage{
drw(data1, data2 = NULL, data3 = NULL, data4 = NULL, data5 = NULL,
    data6 = NULL, data7 = NULL, data8 = NULL, data9 = NULL,
    data10 = NULL, n.datasets, method = "mle", poly.order = 1,
    bayes.n.burn = 3000, bayes.n.sample = 1000)
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
\item{method}{Either \code{"mle"} for maximum likelihood estimation or \code{"bayes"} for posterior sampling.}
\item{poly.order}{The order of the polynomial trend used for the mean function of each time series. The default is 1, corresponding to an intercept and a linear trend in normalized time. Use 0 for the constant-mean damped random walk model.}
\item{bayes.n.burn}{The number of warm-up iterations when \code{method = "bayes"}.}
\item{bayes.n.sample}{The number of posterior samples saved after warm-up when \code{method = "bayes"}.}
}
\value{
The returned object is a list. For \code{method = "mle"}, it contains:
\describe{
\item{beta}{Maximum likelihood estimates of the polynomial trend coefficients. The coefficients are returned as a vector ordered by time series. For each time series, the coefficients correspond to powers 0 through \code{poly.order} of normalized time, u = (t - t_min)/(t_max - t_min). Thus, beta_j0 is the fitted mean at the first normalized time point, and higher-order coefficients describe changes over the unit interval of normalized time, not per day.}
\item{sigma2}{Maximum likelihood estimates of the short-term variance parameters.}
\item{sigma}{Maximum likelihood estimates of the short-term standard deviation parameters.}
\item{tau}{Maximum likelihood estimates of the timescale parameters on the normalized-time scale.}
\item{tau.days}{Maximum likelihood estimates of the timescale parameters on the original time scale. If the input observation times are measured in days, then \code{tau.days} is the estimated timescale in days. It is computed as \code{tau * time.range}.}
\item{rho}{Maximum likelihood estimates of the cross-correlation parameters when \code{n.datasets > 1}; otherwise \code{numeric(0)}.}
\item{time.range}{The range of the combined observation times, \code{max(time) - min(time)}.}
\item{time.min}{The minimum combined observation time.}
\item{data.comb}{The merged data matrix used for fitting.}
}
For \code{method = "bayes"}, \code{beta}, \code{sigma}, \code{tau}, \code{tau.days}, and \code{rho} contain posterior samples, with one row per saved MCMC iteration. The output also includes \code{sigma.accept.rate}, \code{tau.accept.rate}, and \code{rho.accept.rate}.
}
\description{
The function \code{drw} fits univariate and multivariate damped random walk processes to one or more irregularly spaced time series with possibly heteroscedastic measurement errors. The current implementation allows each time series to have a polynomial mean trend in normalized time. This feature is useful in applications such as stock price prediction, where a constant mean may be too restrictive. The likelihood is evaluated by Kalman filtering, and the function returns maximum likelihood estimates or posterior samples of the model parameters.
}
\details{
The multivariate damped random walk process is also known as the Ornstein--Uhlenbeck process or a CARMA(1, 0) process. In the updated model, the long-term mean of the j-th time series is represented as

m_j(u) = beta_j0 + beta_j1 * u + ... + beta_jp * u^p,

where p is \code{poly.order}. The time variable u is the internally normalized observation time,

u = (t - t_min)/(t_max - t_min),

where t_min and t_max are the minimum and maximum combined observation times, respectively. Setting \code{poly.order = 0} recovers the constant-mean specification in the original package.

Because the likelihood is evaluated on normalized time, the estimated \code{tau} values are also on the normalized-time scale. To convert them back to the original time scale, multiply by \code{time.range = max(time) - min(time)}. For example, if the combined observation times span 2,000 days and \code{tau = 0.05}, then the corresponding timescale is \code{0.05 * 2000 = 100} days. The returned object includes this converted value as \code{tau.days}.

The polynomial coefficients in \code{beta} should be interpreted on the same normalized-time scale. For example, with \code{poly.order = 1}, the fitted mean is beta_j0 + beta_j1 * u, so beta_j1 is the total linear change over the normalized interval [0, 1], not the daily slope.

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
res1.mle$tau.days

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
                method = "mle", poly.order = 1)
}
}
\author{Zhirui Hu and Hyungsuk Tak}
\references{Zhirui Hu and Hyungsuk Tak (2020), "Modeling Stochastic Variability in Multi-Band Time Series Data," doi:10.48550/arXiv.2005.08049.}
