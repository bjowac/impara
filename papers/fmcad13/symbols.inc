%\usepackage{dlfltxbcodetips} % for \bigtimes
\usepackage{wrapfig}
\usepackage{multirow}
\usepackage{amsmath}
\usepackage{amssymb,amsfonts,graphicx,stmaryrd}
\usepackage{fourier}
\usepackage{xspace}
\usepackage{cancel}


\usepackage{algorithm} 
\usepackage[noend]{algpseudocode}
\usepackage[unicode]{hyperref}

\usepackage{url}
\usepackage{flushend}

% definition/lemma/proposition evironment for IEEE
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{\bf{Lemma}}
\newtheorem{proposition}[theorem]{\bf{Proposition}}
\newtheorem{corollary}[theorem]{\bf{Corollary}}
\newtheorem{define}[theorem]{\bf{Definition}}

\newenvironment{proof}[1][Proof]{\begin{trivlist}
\item[\hskip \labelsep {\bfseries #1}]}{\end{trivlist}}
\newenvironment{definition}[1][Definition]{\begin{trivlist}
\item[\hskip \labelsep {\bfseries #1}]}{\end{trivlist}}
\newenvironment{example}[1][Example]{\begin{trivlist}
\item[\hskip \labelsep {\bfseries #1}]}{\end{trivlist}}
\newenvironment{remark}[1][Remark]{\begin{trivlist}
\item[\hskip \labelsep {\bfseries #1}]}{\end{trivlist}}

\newcommand{\qed}{\nobreak \ifvmode \relax \else
      \ifdim\lastskip<1.5em \hskip-\lastskip
      \hskip1.5em plus0em minus0.5em \fi \nobreak
      \vrule height0.75em width0.5em depth0.25em\fi}
% end of ... environments

\usepackage{color}

\definecolor{taskyblue}{rgb}{0.44706, 0.56078, 0.81176}         % #728fcf
\definecolor{ta2skyblue}{rgb}{0.20392, 0.39608, 0.64314}        % #3465a4
\definecolor{ta3skyblue}{rgb}{0.12549, 0.29020, 0.52941}        % #204a87


\usepackage{cite}
\usepackage{times}

\usepackage{comment}
\usepackage{subfig}



\newcommand{\prog}[1]{\textnormal{\scshape#1}}



% tikz
\usepackage{tikz}

% \usetikzlibrary{external} 

\usetikzlibrary{arrows,decorations,shapes,shadows}

\tikzset{
  ashadow/.style={opacity=.25, shadow xshift=0.07, shadow yshift=-0.07},
}

% colors

% - shades of gray 
\tikzstyle{lightgray}=[fill=black!5]
\tikzstyle{gray}=[fill=black!20]
\tikzstyle{darkgray} = [fill=black!35]

% - true colors
\tikzstyle{lightblue} = [fill=blue!5]
\tikzstyle{lightred} = [fill=red!5]

\tikzstyle{ord}=[rounded rectangle, draw,minimum size=15pt,inner sep=1pt] % "ordinary" state / block (as opposed to goal)
\tikzstyle{goal}=[rounded rectangle, very thick,draw,minimum size=15pt,inner sep=1pt, fill=white] % goal state / block

\tikzstyle{trans}=[>=angle 90,->,line width=0.02cm]
\tikzstyle{player}=[rectangle,fill=black,minimum size=3pt,inner sep=0pt]
\tikzstyle{distribution}=[circle,fill=black,minimum size=3pt,inner sep=0pt]


% the ellipses
\tikzstyle{transparent} = [fill opacity=0.05]




% Some abbrebviations

% tools
\newcommand{\blast}{\textsc{Blast}\xspace}
\newcommand{\spin}{\textsc{Spin}\xspace}
\newcommand{\impact}{\textsc{Impact}\xspace}
\newcommand{\threader}{\textsc{Threader}\xspace}


% program

\newcommand{\init}{\ensuremath{\mathit{init}}}
\newcommand{\program}{\ensuremath{\mathcal P}}


% states
\newcommand{\states}{S}
\newcommand{\lstates}{\ensuremath{S_{\mathit{local}}}}
\newcommand{\sstates}{\ensuremath{S_{\mathit{shared}}}}

% variables
\newcommand{\vars}{V}
\newcommand{\lvars}{\ensuremath{V_{\mathit{local}}}}
\newcommand{\svars}{\ensuremath{V_{\mathit{shared}}}}


% transitions
\newcommand{\transby}[1]{\overset{#1}\rightarrow}
\newcommand{\transbystar}[1]{\overset{#1}{\leadsto}}

% paths
\newcommand{\pathsequence}{\ensuremath{(\locvec_0,\thread_0,a_0,\locvec_1) \ldots (\locvec_{N-1},\thread_{N-1},a_{N-1},\locvec_N)}}

% partial order
\newcommand{\independent}[2]{#1\ ||\ #2}
\newcommand{\dependent}[2]{#1\ \cancel{||}\ #2}

\newcommand{\thread}{\ensuremath{T}}
\newcommand{\threads}{\ensuremath{\mathcal T}}
\newcommand{\spotlight}{\ensuremath{\mathcal S}}


\newcommand{\threadlocs}{\ensuremath{{L}_t}}
\newcommand{\locs}{\ensuremath{L}}

%\newcommand{\locvec}{\ensuremath{\mathfrak{l}}}
%\newcommand{\locvecinit}{\ensuremath{\mathfrak{l}^{i}}}

\newcommand{\locvec}{\ensuremath{\bar{l}}}
\newcommand{\locvecinit}{\ensuremath{\overline{l_i}}}

\newcommand{\locvecs}{\ensuremath{L_G}}

\newcommand{\locinit}{\ensuremath{l^{i}}}
\newcommand{\locfinal}{\ensuremath{l^{\lightning}}}

\newcommand{\actions}{\ensuremath{A}}


\newcommand{\edges}{\ensuremath{E}}

\newcommand{\wff}{\ensuremath{\mathcal F}}


% ART
\newcommand{\art}{\ensuremath{\mathcal A}}

% algorithm


\newcommand{\covers}{\ensuremath{\triangleright}}
\newcommand{\pcmap}{\ensuremath{\M_v}}

\newcommand{\annotation}{\ensuremath{\phi}}
\newcommand{\start}{\ensuremath{\epsilon}}

\newcommand{\final}{\ensuremath{final}}

\newcommand{\formula}{\ensuremath{\mathcal F}}

\newcommand{\leaf}{\ensuremath{\text{\leafNE}}}


\newcommand{\dporexpand}{Expand$_\Diamond$}
\newcommand{\dporclose}{Close$_\Diamond$}
\newcommand{\dporskip}{Skip$_\Diamond$}

% comments
\newcommand{\dk}[1]{\marginpar{\ \color{red}   \ DK: #1\ \color{black}}}
\newcommand{\jo}[1]{\marginpar{\ \color{blue}   \ JO: #1\ \color{black}}}
\newcommand{\bw}[1]{{\ \color{blue}   \ BW: #1\ \color{black}}}
