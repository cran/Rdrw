\name{drw}
\alias{drw}
\title{Fitting univariate and multiviarate damped random walk processes}
\usage{
drw(data1, data2, data3, data4, data5, 
    data6, data7, data8, data9, data10,
    n.datasets, method = "mle",
    bayes.n.burn, bayes.n.sample,
    mu.UNIFprior.range = c(-30, 30),
    tau.IGprior.shape = 1, tau.IGprior.scale = 1,
    sigma2.IGprior.shape = 1, sigma2.IGprior.scale = 1e-7)
}
\arguments{
\item{data1}{An (\eqn{n_1} by 3) matrix for time series data 1. The first column has \eqn{n_1} observation times, the second column contains \eqn{n_1} measurements (magnitudes), the third column includes \eqn{n_1} measurement error standard deviations. If the measurement error standard deviations are unknown, the third column must be a vector of \eqn{n_1} zeros.
}
\item{data2}{Optional if more than one time series data set are available. An (\eqn{n_2} by 3) matrix for time series data 2. The first column has \eqn{n_2} observation times, the second column contains \eqn{n_2} measurements/observations/magnitudes, the third column includes \eqn{n_2} measurement error standard deviations. If the measurement error standard deviations are unknown, the third column must be a vector of \eqn{n_2} zeros.
}
\item{data3}{Optional if more than two time series data sets are available. An (\eqn{n_3} by 3) matrix for time series data 3. The first column has \eqn{n_3} observation times, the second column contains \eqn{n_3} measurements/observations/magnitudes, the third column includes \eqn{n_3} measurement error standard deviations. If the measurement error standard deviations are unknown, the third column must be a vector of \eqn{n_3} zeros.
}
\item{data4}{Optional if more than three time series data sets are available. An (\eqn{n_4} by 3) matrix for time series data 4. The first column has \eqn{n_4} observation times, the second column contains \eqn{n_4} measurements/observations/magnitudes, the third column includes \eqn{n_4} measurement error standard deviations. If the measurement error standard deviations are unknown, the third column must be a vector of \eqn{n_4} zeros.
}
\item{data5}{Optional if more than four time series data sets are available. An (\eqn{n_5} by 3) matrix for time series data 5. The first column has \eqn{n_5} observation times, the second column contains \eqn{n_5} measurements/observations/magnitudes, the third column includes \eqn{n_5} measurement error standard deviations. If the measurement error standard deviations are unknown, the third column must be a vector of \eqn{n_5} zeros.
}
\item{data6}{Optional if more than five time series data sets are available. An (\eqn{n_6} by 3) matrix for time series data 6. The first column has \eqn{n_6} observation times, the second column contains \eqn{n_6} measurements/observations/magnitudes, the third column includes \eqn{n_6} measurement error standard deviations. If the measurement error standard deviations are unknown, the third column must be a vector of \eqn{n_6} zeros.
}
\item{data7}{Optional if more than six time series data sets are available. An (\eqn{n_7} by 3) matrix for time series data 7. The first column has \eqn{n_7} observation times, the second column contains \eqn{n_7} measurements/observations/magnitudes, the third column includes \eqn{n_7} measurement error standard deviations. If the measurement error standard deviations are unknown, the third column must be a vector of \eqn{n_7} zeros.
}
\item{data8}{Optional if more than seven time series data sets are available. An (\eqn{n_8} by 3) matrix for time series data 8. The first column has \eqn{n_8} observation times, the second column contains \eqn{n_8} measurements/observations/magnitudes, the third column includes \eqn{n_8} measurement error standard deviations. If the measurement error standard deviations are unknown, the third column must be a vector of \eqn{n_8} zeros.
}
\item{data9}{Optional if more than eight time series data sets are available. An (\eqn{n_9} by 3) matrix for time series data 9. The first column has \eqn{n_9} observation times, the second column contains \eqn{n_9} measurements/observations/magnitudes, the third column includes \eqn{n_9} measurement error standard deviations. If the measurement error standard deviations are unknown, the third column must be a vector of \eqn{n_9} zeros.
}
\item{data10}{Optional if more than nine time series data sets are available. An (\eqn{n_{10}} by 3) matrix for time series data 10. The first column has \eqn{n_{10}} observation times, the second column contains \eqn{n_{10}} measurements/observations/magnitudes, the third column includes \eqn{n_{10}} measurement error standard deviations. If the measurement error standard deviations are unknown, the third column must be a vector of \eqn{n_{10}} zeros. The current version of package allows up to ten time series data sets. If users have more than ten time series data sets to be modeled simultaneously, please contact the authors.
}

\item{n.datasets}{The number of time series data sets to be modeled simultaneously. An integer value inclusively between 1 to 10. For example, if "\code{n.datasets = 3}", then users must enter \code{data1}, \code{data2}, and \code{data3} as inputs of \code{drw}.}

\item{method}{If \code{method = "mle"}, it returns maximum likelihood estimates of the model parameters. If \code{method = "bayes"} it produces posterior samples of the model parameters.}

\item{bayes.n.burn}{Required for \code{method = "bayes"}. The number of warming-up iterations for a Markov chain Monte Carlo method.}

\item{bayes.n.sample}{Required for \code{method = "bayes"}. The size of a posterior sample for each parameter for a Markov chain Monte Carlo method.}

\item{mu.UNIFprior.range}{Required for \code{method = "bayes"}. The range of the Uniform prior on each long-term avaerage \eqn{\mu_j}of the process, where \eqn{j} goes from 1 to the total number of time series data sets. The default range is (\eqn{-30, 30}) for astronomical applications.}

\item{tau.IGprior.shape}{Required for \code{method = "bayes"}. The shape parameter of the invserse-Gamma prior on each timescale \eqn{\tau_j} of the process, where \eqn{j} goes from 1 to the total number of time series data sets. The default shape parameter is one for astronomical applications.}

\item{tau.IGprior.scale}{Required for \code{method = "bayes"}. The scale parameter of the invserse-Gamma prior on each timescale \eqn{\tau_j}, where \eqn{j} goes from 1 to the total number of time series data sets. The default scale parameter is one for astronomical applications.}

\item{sigma2.IGprior.shape}{Required for \code{method = "bayes"}. The shape parameter of the invserse-Gamma prior on each short-term variability (variance) \eqn{\sigma^2_j}, where \eqn{j} goes from 1 to the total number of time series data sets. The default shape parameter is one for astronomical applications.}

\item{sigma2.IGprior.scale}{Required for \code{method = "bayes"}. The scale parameter of the invserse-Gamma prior on each short-term variability (variance) \eqn{\sigma^2_j}, where \eqn{j} goes from 1 to the total number of time series data sets. The default shape parameter is 1e\eqn{-7} for astronomical applications.}

}
\value{
The outcomes of \code{drw} are composed of:
\describe{
\item{mu}{The maximum likelihood estimate(s) of the long-term average(s) if \code{method} is "mle", and the posterior sample(s) of the long-term average(s) if \code{method} is "bayes". In the former case (mle), it is a vector of length \eqn{k}, where \eqn{k} is the number of time series data sets used. In the later case (bayes), it is an (\eqn{m} by \eqn{k}) matrix where \eqn{m} is the size of the posterior sample.}
\item{sigma}{The maximum likelihood estimate(s) of the short-term variability (standard deviation) parameter(s) if \code{method} is "mle", and the posterior sample(s) of the short-term variability parameter(s) if \code{method} is "bayes". In the former case (mle), it is a vector of length \eqn{k}, where \eqn{k} is the number of time series data sets used. In the later case (bayes), it is an (\eqn{m} by \eqn{k}) matrix where \eqn{m} is the size of the posterior sample.}
\item{tau}{The maximum likelihood estimate(s) of the timescale(s) if \code{method} is "mle", and the posterior sample(s) of the timescale(s) if \code{method} is "bayes". In the former case (mle), it is a vector of length \eqn{k}, where \eqn{k} is the number of time series data sets used. In the later case (bayes), it is an (\eqn{m} by \eqn{k}) matrix where \eqn{m} is the size of the posterior sample.}
\item{rho}{Only when more than one time series data set are used. The maximum likelihood estimate(s) of the (cross-) correlation(s) if \code{method} is "mle", and the posterior sample(s) of the (cross-) correlation(s) if \code{method} is "bayes". In the former case (mle), it is a vector of length \eqn{k(k-1)/2}, where \eqn{k} is the number of time series data sets used, i.e., \eqn{\rho_{12}, \ldots, \rho_{1k}, \rho_{23}, \ldots, \rho_{2k}, \ldots, \rho_{k-1, k}}. In the later case (bayes), it is an (\eqn{m} by \eqn{k(k-1)/2}) matrix where \eqn{m} is the size of the posterior sample.}
\item{mu.accept.rate}{Only when \code{method} is "bayes". The MCMC acceptance rate(s) of the long-term average parameter(s).}
\item{sigma.accept.rate}{Only when \code{method} is "bayes". The MCMC acceptance rate(s) of the short-term variability parameter(s).}
\item{tau.accept.rate}{Only when \code{method} is "bayes". The MCMC acceptance rate(s) of the timescale(s).}
\item{rho.accept.rate}{Only when more than one time series data set are used with \code{method = "bayes"}. The MCMC acceptance rate(s) of the (cross-) correlation(s).}
\item{data.comb}{The combined data set if more than one time series data set are used, and data1 if only one time series data set is used. This output is only available when \code{method} is set to "bayes".}
}
}
\description{
The function \code{drw} fits univariate and multivariate damped random walk processes on multiple time series data sets possibly with known measurement error standard deviations via state-space representation. This function \code{drw} evaluates the resulting likelihood function of the model parameters via Kalman-filtering whose minimum complexity is linear in the number of unique observation times. The function returns the maximum likelihood estimates or posterior samples of the model parameters. For astronomical data analyses, users need to pay attention to loading the data because R's default is to load only seven effective digits; see details below.
}
\details{
 The multivariate damped random walk process \eqn{{\bf X}(t)} is defined by the following stochastic differential equation:
  \deqn{d {\bf X}(t) = -D_{{\bf\tau}}^{-1}({\bf X}(t) - {\bf\mu})dt + D_{{\bf\sigma}} d {\bf B}(t),}
where \eqn{{\bf X}(t)=\{X_1(t), \ldots, X_k(t)\}} is a vector of \eqn{k} measurements/observations/magnitudes of the \eqn{k} time series data sets in continuous time \eqn{t\in R}, \eqn{D_{\bf\tau}} is a \eqn{k\times k} diagonal matrix whose diagonal elements are \eqn{k} timescales with each \eqn{\tau_j} representing the  timescale of the \eqn{j}-th time series data, \eqn{{\bf\mu}=\{\mu_1, \ldots, \mu_k\}} is a vector for long-term averages of the \eqn{k} time series data sets, \eqn{D_{{\bf\sigma}}} is \eqn{k\times k} diagonal matrix whose diagonal elements are short-term variabilities (standard deviation) of \eqn{k} time series data sets, and finally \eqn{{\bf B}(t)=\{B_1(t), \ldots, B_k(t)\}} is a vector for \eqn{k} standard Brownian motions whose \eqn{k(k-1)/2} pairwise correlations are modeled by correlation parameters \eqn{\rho_{jl}~(1\le j<l\le k)} such that \eqn{dB_j(t)B_l(t) = \rho_{jl} dt}.


We evaluate this continuous-time process at \eqn{n} discrete observation times \eqn{{\bf t} = \{t_1, \ldots, t_n\}}.  The observed data \eqn{{\bf x} = \{x_1, \ldots, x_n\}} are multiple time series data measured at irregularly spaced observation times \eqn{{\bf t}} with possibly known measurement error standard deviations, \eqn{\delta=\{\delta_1, \ldots, \delta_n\}}. Since one or more time series observations can be measured at each observation time \eqn{t_i}, the length of a vector \eqn{x_i} can be different, depending on how many time series observations are available at the \eqn{i}-th observation time. We assume that these observed data \eqn{{\bf x}} are realizations of the latent time series data sets \eqn{{\bf X(t)} = \{{\bf X}(t_1), \ldots, {\bf X}(t_n)\}} with Gaussian measurement errors whose variances are \eqn{\delta}. This is a typical setting of state-space modeling. We note that if the measurement error variances are unknown, \eqn{\delta} must be set to zeros, which means that the observed data directly measure the latent values.

Please note that when astronomical time series data are loaded on R by \code{read.table}, \code{read.csv}, etc., some decimal places of the the observation times are automatically rounded because R's default is to load seven effective digits. For example, R will load the observation time 51075.412789 as 51075.41. This default will produce many ties in observation times even though there is actually no tie in observation times. To prevent this, please type "\code{options(digits = 11)}" before loading the data if the observation times are in seven effective digits.
}
\examples{
########## Fitting a univariate damped random walk process

##### Fitting a univariate damped random walk process based on a simulation

n1 <- 20 
# the number of observations in the data set

obs.time1 <- cumsum(rgamma(n1, shape = 3, rate = 1))
# the irregularly-spaced observation times 

y1 <- rnorm(n1)
# the measurements/observations/magnitudes

measure.error.SD1 <- rgamma(n1, shape = 0.01)
# optional measurement error standard deviations, 
# which is typically known in astronomical time series data
# if not known in other applications, set them to zeros, i.e.,
# measure.error.SD1 <- rep(0, n1)

data1 <- cbind(obs.time1, y1, measure.error.SD1)
# combine the single time series data set into an n by 3 matrix

# Note that when astronomical time series data are loaded on R (e.g., read.table, read.csv), 
# the digits of the observation times are typically rounded to seven effective digits.
# That means rounding may occur, which produces ties in observation times even though
# the original observation times are not the same.
# In this case, type the following code before loading the data.
# options(digits = 11)

res1.mle <- drw(data1 = data1, n.datasets = 1, method = "mle")
# obtain maximum likelihood estimates of the model parameters and 
# assign the result to object "res1.mle"

names(res1.mle)
# to see the maximum likelihood estimates,
# type "res1.mle$mu", "res1.mle$sigma", "res1.mle$tau"

\donttest{
res1.bayes <- drw(data1 = data1, n.datasets = 1, method = "bayes", 
                  bayes.n.burn = 10, bayes.n.sample = 10)
}
# obtain 10 posterior samples of each model parameter and
# save the result to object "res1.bayes"

# names(res1.bayes)
# to work on the posterior sample of each parameter, try 
# "res1.bayes$mu.accept.rate", "res1.bayes$sigma.accept.rate", "res1.bayes$tau.accept.rate"
# "hist(res1.bayes$mu)", "mean(res1.bayes$mu)", "sd(res1.bayes$mu)",
# "median(log(res1.bayes$sigma, base = 10))", 
# "quantile(log(res1.bayes$tau, base = 10), prob = c(0.025, 0.975))"


##### Fitting a multivariate damped random walk process based on simulations

n2 <- 10 
# the number of observations in the second data set

obs.time2 <- cumsum(rgamma(n2, shape = 3, rate = 1))
# the irregularly-spaced observation times of the second data set

y2 <- rnorm(n2)
# the measurements/observations/magnitudes of the second data set

measure.error.SD2 <- rgamma(n2, shape = 0.01)
# optional measurement error standard deviations of the second data set, 
# which is typically known in astronomical time series data
# if not known in other applications, set them to zeros, i.e.,
# measure.error.SD2 <- rep(0, n2)

data2 <- cbind(obs.time2, y2, measure.error.SD2)
# combine the single time series data set into an n by 3 matrix

\donttest{
res2.mle <- drw(data1 = data1, data2 = data2, n.datasets = 2, method = "mle")
}
# obtain maximum likelihood estimates of the model parameters and 
# assign the result to object "res2.mle"

\donttest{
res2.bayes <- drw(data1 = data1, data2 = data2, n.datasets = 2, method = "bayes", 
                  bayes.n.burn = 10, bayes.n.sample = 10)
}
# obtain 10 posterior samples of each model parameter and
# save the result to object "res2.bayes"

# names(res2.bayes)
# to work on the posterior sample of each parameter, try 
# "hist(res2.bayes$mu[, 1])", "colMeans(res2.bayes$mu)", "apply(res2.bayes$mu, 2, sd)",
# "hist(log(res2.bayes$sigma[, 2], base = 10))", 
# "apply(log(res2.bayes$sigma, base = 10), 2, median)", 
# "apply(log(res2.bayes$tau, base = 10), 2, quantile, prob = c(0.025, 0.975))"
}
\author{
Zhirui Hu and Hyungsuk Tak
}
\references{
    Zhirui Hu and Hyungsuk Tak (2020+), "Modeling Stochastic Variability in  Multi-Band Time Series Data," arXiv:2005.08049.
}
