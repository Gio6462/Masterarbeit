\ProvidesPackage{dsfont}
  [1995/08/01 v0.1 Double stroke roman fonts]

\def\ds@whichfont{dsrom}
\DeclareOption{sans}{\def\ds@whichfont{dsss}}
\ProcessOptions\relax

\DeclareMathAlphabet{\mathds}{U}{\ds@whichfont}{m}{n}
\endinput
\documentclass[12pt]{article}

% This first part of the file is called the PREAMBLE. It includes
% customizations and command definitions. The preamble is everything
% between \documentclass and \begin{document}.

\usepackage[margin=1in]{geometry}  % set the margins to 1in on all sides
\usepackage{amsmath}               % great math stuff
\usepackage{amsfonts}              % for blackboard bold, etc
\usepackage{amsthm}                % better theorem environments


% various theorems, numbered by section

\newtheorem{thm}{Theorem}[section]
\newtheorem{lem}[thm]{Lemma}
\newtheorem{prop}[thm]{Proposition}
\newtheorem{cor}[thm]{Corollary}
\newtheorem{conj}[thm]{Conjecture}

\DeclareMathOperator{\id}{id}

\newcommand{\bd}[1]{\mathbf{#1}}  % for bolding symbols
\newcommand{\R}{\mathbb{R}}      % for Real numbers
\newcommand{\Z}{\mathbb{Z}}
\newcommand{\Prob}{\mathds{P}} 
\newcommand*\dif{\mathop{}\!\mathrm{d}}


\begin{document}


\nocite{*}

\title{TASEP}

\author{Giovanni D'Urso\\ 
Department of Mathematics \\
Uni Bonn \\
Bonn, Germany}

\maketitle

\begin{abstract}

\end{abstract}


\section{Introduction}

Deterministic initial configuration: on $\Z_{-}$ we place a particle every second position
Random initial configuration: Bernulli on $\Z_{-}$ with intensity $\lambda= \frac{1}{2}$.


\section{}
In the following Proposition we derive an expression of the trasition probability from time $t=0$ to time $t$ for $N$ particles with Bernulli random initial configuration with intensity $\lambda$ on $\Z_{-}$. The Proposition is based  on (large time asymp), where deterministic initial confifirations are considered.

\begin{prop}\label{tran:prob}
Consider $N$ particles on $\Z_{-}$ with Bernulli random initial configuration. Denote its transion probability until time $t$ by 
\begin{equation}
 G(x_N, \dots, x_1;t)=\Prob_{\lambda}[x_i(t)= x_i,  1\leq i \leq N],
\end{equation}
where $\Prob_{\lambda}$ is the probability starting with the Bernulli initial configuration.
Then, 
\begin{equation}
G(x_N, \dots, x_1;t)=(1-\lambda)^Ne^{-Nt}\det[F_{k,l}(x_{N+1-l}-y_{N+1-k},t)]_{1\leq k,l \leq N}
\end{equation}
 with parameters $y_i=-i, 1\leq i \leq N$ and 
\begin{equation} 
F_{k,l}(x,t)=\frac{1}{2\pi i} \oint_{|z|\ll1}  \dif z z^{x-1}(1-z)^{k-l}\frac{e^{\frac{t}{z}}}{1-%\frac{1}{2}
\lambda z}
\end{equation} where ${|z|\ll1}$ is any anticlockwise oriented circle which includes only the pole at $z=0$.
\begin{proof}
We first prove that the initial condition is satisfied. We have \[ F_{k,l}(x,0)=\frac{1}{2\pi i} \oint_{|z|\ll1}  \dif z z^{x-1}(1-z)^{k-l}\frac{1}{1-%\frac{1}{2}
\lambda z}\]
We observe that:\\ (a) $F_{k,l}(x,0)=0$ if $k\geq 1$, because the pole at $z=0$ disappear. Thus, if the determinant is non-zero, then $x_i\leq y_i for all i\in\{1,\dots,n\}$. Indeed if $x_i>y_i$ for some $i$, then $x_{i-a}>y_{i+b}$ for any $a,b\geq 0$ and by the observation a corner of the matrix has zero entries, which implies that the deter,minant is zero. We can assume then $x_i\leq y_i, i=1,\dots, N$.\\
(b) For $k\geq l$ and $x\leq l-k +1$, 
\begin{equation}\label{formF} F_{k,l}(x,0)=(\lambda-1)^{k-l}\lambda^{-x-k+l+1}.
\end{equation} To see this, note that for $k\geq l$, we have
\begin{align}
F_{k,l}(x,0)&=\frac{1}{2\pi i} \oint_{|z|\ll1}  \dif z\, z^{x-1}(1-z)^{k-l}\frac{1}{1-\lambda z}\\
		&=\frac{1}{2\pi i} \oint_{|w|\gg1}  \dif w\, \frac{1}{w}(1-1/w)^{k-l}w^{-x+1}\frac{1}{1-\lambda/w}\\
		&=\frac{1}{2\pi i} \oint_{|w|\gg1}  \dif w\, (w-1)^{k-l}w^{-x-k+l+1}\frac{1}{w-\lambda}
\end{align}

and, if $x\leq l-k +1$, the only pole is $w=1$.\\
Now, since $x_{N+1-l}-y_{N+1-k}\leq l-k$ (because $x_{N+1-l}\leq -(N+1-l) \,\mbox{and}\,\, y_{N+1-k}=-(N+1-k))$, we have that~\ref{formF} holds for $(x_{N+1-l}-y_{N+1-k},0)$: 
\begin{equation}
F_{k,l}(x_{N+1-l}-y_{N+1-k},0)=(\lambda-1)^{k-l}\lambda^{y_{N+1-k}-x_{N+1-l}-k+l+1}.
\end{equation}
Define
\begin{subequations}
\begin{align}
        A_n&=(\lambda -1)^n\lambda^{y_{N+1-n}-n+1},\\
        B_n&=(\lambda -1)^{-n}\lambda^{-x_{N+1-n}+n}.
\end{align}
\end{subequations}
Then we have \[F_{k,l}(x_{N+1-l}-y_{N+1-k},0)=A_kB_l \,\,\mbox{for}\, k\geq l. \]
We apply now the Lemma (appendix) to conclude that the determinant is equal to
\begin{subequations}
\begin{align}
B_1(B_2A_1-F_{1,2}(x_{N-1}-y_{N},0))(B_3A_2-F_{2,3}(x_{N-2}-y_{N-1},0))&\dots(B_NA_{N-1}- F_{N-1, N}\\&(x_1-y_2,0))A_N.
\end{align}
\end{subequations}
Further, 
\begin{subequations}
\begin{align}
F_{k,k+1}(x_{N-k}-y_{N+1-k},0)&=\frac{1}{2\pi i} \oint_{|w|\gg1}  \dif w\, \frac{1}{(w-1)(w-\lambda)}w^{y_{N+1-k}-x_{N-k}+2}\\
&=\frac{1}{\lambda-1}\frac{1}{2\pi i} \oint_{|w|\gg1}  \dif w\, \frac{1}{(w-\lambda)}-\frac{1}{w-1}w^{y_{N+1-k}-x_{N-k}+2}.
\end{align}
\end{subequations}
Since $x_{N-k}\leq y_{N-k}=y_{N+1-k}+1$, there is no pole at at $w=0$ and we obtain:
\[F_{k,k+1}(x_{N-k}-y_{N+1-k},0)=\frac{1}{\lambda-1}(\lambda^{y_{N+1-k}-x_{N-k}+2}-1).\]

On the other hand,
\begin{subequations}
\begin{align}
B_{k+1}A_{k}&=\frac{1}{\lambda -1}\lambda^{-x_{N-k}+y_{N+1-k}+2}\\
B_{k+1}A_{k}-F_{k,k+1}(x_{N-k}-y_{N+1-k},0)&=\frac{1}{\lambda -1}.
\end{align}
\end{subequations}
Thus the determinant equals $\lambda^{-x_N -N+1}$ and hence we obtain
\[G(x_N, \dots, x_1;0)=(1-\lambda)^N\lambda^{-x_N -N+1}\]

which coincides with the probability of having N particles wich are independently Bernoulli distributed with intensity $\lambda$ at fixed sites $(x_1>x_2>\dots>x_N )$ with $x_i\in\Z_{-}$. Indeed,

\begin{equation}
\Prob_{\lambda}[x_i(t)= x_i,  1\leq i \leq N]=..
\end{equation}
by the independence of the particles' positions.
\end{proof}
\end{prop}






\subsection{Accents}

Don't be na\"{\i}ve, ordering \'a la carte is expensive. Don't use \"o
when you write Erd\H{o}s. Be honest; don't put up a fa\c{c}ade. Use
H\^opital's rule. 

Then we would like to see....




\section{Apendix}



\bibliographystyle{plain}

\bibliography{paper}


\end{document}
