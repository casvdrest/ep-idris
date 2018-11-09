\documentclass[11pt,a4paper]{article}

% Quotes
\usepackage{epigraph}
\renewcommand{\epigraphwidth}{8cm}

\usepackage{geometry}

\usepackage[utf8]{inputenc}
%include polycode.fmt

%format implies = "\Rightarrow"
%format simeq   = "\simeq"
%format bottom  = "\bot" 
%format forall  = "\forall"
%format exists  = "\exists" 
%format pipe = "|"
%format dpair = "\Sigma" 
\usepackage{multicol}

% Math
\usepackage{amssymb}
% Tables
\usepackage{amsmath}

\usepackage{minted}

% Colors
\usepackage{xcolor, color, colortbl}
\colorlet{gray}{gray!70}
\colorlet{green}{green!50}
\definecolor{darkblue}{HTML}{1D577A}
\definecolor{rred}{HTML}{C03425}
\definecolor{darkgreen}{HTML}{8BB523}
\definecolor{ppurple}{HTML}{6B1B7F}
\definecolor{pblack}{HTML}{000000}
\definecolor{darkyellow}{HTML}{C0B225}

% Links
\usepackage{hyperref}
\definecolor{linkcolour}{rgb}{0,0.2,0.6}
\hypersetup{colorlinks,breaklinks,urlcolor=linkcolour,linkcolor=linkcolour,citecolor=blue}

% Geometry
%\usepackage{titling}
%\setlength{\droptitle}{-7em}

\title{Experimentation Project: Safer Shell Scripts Using Dependent Types}
\author{Cas van der Rest}
\date{November 2018}

\begin{document}

\maketitle

\section{Introduction}

Little safety is provided when executing third party shell scripts. Usually there is no way to know anything about the effects of a script on a system without thorough inspection of its contents, a task 
that is preferably avoided: it is cumbersome at best, and realistically unfeasible in many cases. Furthermore, a script is often executed with much more \textit{capabilities} than it needs. In the context 
of a shell, a script usually receives whatever authority the user that executes it has on the system, a concept known as \textit{ambient authority}. Depending on the role of the user this in itself can be 
problematic, were it not for the fact that it is not uncommon for a user to execute scripts with root privileges in case the script needs to modify something that is outside the user's authority. 

Execution of a script from an outside source would proceed with much more confidence if it would provide some kind of metadata describing its effects, in a format that is easy for a user to inspect. Of 
course, this only works if we know that a script will not act outside what is described in its metadata.

In this project, I have attempted to provide a solution that mitigates these issues by embedding a small subset of Bash into Idris\cite{brady13}, utilizing its dependent type system to model a script's 
behaviour, and statically enforce that the claims made by a script are respected. 

\section{Related Work}

The approach taken in the project is largely based on \textit{Shill}\cite{moore14}, a scripting language developed at Harvard University. Shill is based around the \textit{principle of least privilege} (a script should have no more authority than it strictly needs), and takes a sanbox-based approach to enforcing this principle. 

Every Shill script comes with a contract, describing the \textit{capabilities} of script; i.e. the resources it requires to run. The sandbox will only allow a script access to resources that are part of it's capabilities. Similarly, native shell commands that are called from a Shill script are also executed in the sanbox, and thus are restricted in the same way. 

An example contract of a script taking one input parameter (called $input\_file$ ) could be: 

\begin{code}

provide: 
	{ input_file : is_file land writable } -> Void

\end{code}

Proclaiming that the input parameter should refer to an existing file, and that the script will need write permissions on that file. Shill contracts consist of a precondition and a return type. An example of a script that could utilize the above contract is: 

\begin{code}
if is_file(input_file) && has_ext(input_file, "jpg") then
	append("Hello, World!", path(input_file));
\end{code}

Although Shill's API provides the necessary tools to specify fine-grained authority for scripts, all enforcement of contracts happens dynamically. This comes with the obvious downside of how to deal with scripts that fail dynamically halfway through their execution. Preferably we would deal with this scenario by preventing scripts that violate their contract from executing at all!

\section{Project Scope}

Bash is a \textit{very} elaborate shell, and to try to capture all its nuances in this project is clearly not a reasonable objective. 

At the very least, we would like to cover some very basic scenarios where scripts try to access files and/or directories. An example of such a script would be: 

\begin{minted}[escapeinside=||,mathescape=true]{bash}
ls /home/cas 
cat /etc/shadow 
\end{minted}

The corresponding Shill contract would look something like the following: 

\begin{code}
provide: 
	{  "/home/cas" : is_dir && readable
	,  "/etc/shadow" : is_file && readable 
	} -> Void
\end{code}

We can identify several properties of files and directories we would like to be able to specify and assert by means of a precondition. Most notably whether a resource is an existing file or directory and if a user has certain authority over that resource. 

Merely a precondition is obviously not sufficient to specify more complex behaviour. In particular, dependencies between different parts of the script can be hard to capture. Consider the following snippet: 

\begin{minted}{bash}
touch file.txt 
cat file.txt
\end{minted}

The \texttt{touch} command does not care whether \textit{file.txt} already exists, but \texttt{cat} fails in that case. However, requiring that \textit{file.txt} exists makes the precondition to strong; a successful execution of \texttt{touch file.txt} guarantees that \textit{file.txt} exists when we arrive at the \texttt{cat} statement. 

\subsection{Command Line Options}
The behaviour of a command (and by extension the required parameters and return type) often depends on the various flags and options that were specified. Invoking the \texttt{man} command for any of the more common commands reveals a vast array of possibilities. To circumvent the problems this implies for a formalization of a command's behaviour, we assume a simplified model in which any single command is assumed to have a fixed set of parameters and return type. 

\subsection{File System}

\section{Implementation}

\subsection{Filesystem}

In order to reason about the effects of a command on a filesystem, we need some kind of abstract representation. The chosen representation is a rose tree with an additional constructor for leafs, in order to be able to distinguish between files (leafs of the tree) and empty directories (nodes with no children). Both nodes and leafs contain metadata of that particular vertex, including permissions, name and the type (file or directory). The contents of a file are not recorded. 

This results in the following datatype definition: 

\begin{code}

data FSTree  =   FSNode FileInfo (List FSTree)  -- Directories
             |   FSLeaf FileInfo                -- Files

\end{code}

It should be obvious that leafs are only meant to contain files, and nodes are supposed to contain directories. 

\subsection{Predicates}

The programmer may use standard predicate logic to express a commands behaviour. As discussed before, this by no means enough to capture all the intricacies of script's behaviour, but we should at least be able to rule out certain errors by defining a sufficiently strong precondition. 

\subsubsection{Embedding of Predicates}

In a dependently typed language, propositions are commonly defined as a type, and justified by supplying a definition that inhabits said type. Converting a formula in predicate logic to its corresponding type is relatively straightforward. I assume the following mapping: 

\begin{code}

true    				simeq  ()  
false   		 		simeq  bottom (Void)
P && Q  		 		simeq  (P, Q)
P || Q  		 		simeq  Either P Q 
P implies Q     simeq  P -> Q
forall x : P x  simeq  {a : x} -> P a
exists x : P x  simeq  dpair(x:A, P(x))

\end{code}

Sigma types are modelled as dependent pairs in Idris. For convinience, the infix constructor \texttt{><} is used in place of \texttt{DPair}. A value of type \texttt{(A >< P)} is constructed using \texttt{**}, e.g. \texttt{(value ** proof)}. 

A deep embedding exists for predicates in order to allow for easier manipulation of predicates, and more readable code. For example, consider the precondition of two subsequent \texttt{echo} commands:

\begin{code}
true && (forall (x:String):true && (forall (y:String):true)) 
\end{code}

This corresponds to the following type:

\begin{code}
((), {x : String} -> ((), {y : String} -> ()))
\end{code}

Using a deep embedding for predicates, we can simply write: 

\begin{code}
[[..]] T && (Forall String (\x => T && Forall String (\y => T)))
\end{code}

Both expressions yield the same value, and are interchangeable. The \texttt{[[..]]} modifier is simply defined as a function with type $Predicate s \rightarrow s \rightarrow Type$ that yields an appropriate type for a given predicate. 

The $Predicate$ datatype in its entirety is defined as follows: 

\begin{code}
data Predicate : Type -> Type where 
  data Predicate : Type -> Type where 
  (/\)  : Predicate s -> Predicate s -> Predicate s
  (:=>) : Predicate s -> Predicate s -> Predicate s
  Forall : (a : Type) -> (a -> Predicate s) -> Predicate s
  Exists : (a : Type) -> (a -> Predicate s) -> Predicate s
  Atom : (s -> Type) -> Predicate s
  T : Predicate s
  F : Predicate s
\end{code}

The $Atom$ constructor allows for the inclusion of properties that reason about values of the type that a predicate ranges over. For example, suppose we are constructing a predicate that ranges over natural numbers and want to specify that a number is equal to some nuber $m$. We could use the following atomic predicate: 

\begin{code}
isM : Nat -> Nat -> Type 
isM m = [[..]] (Atom $ (\n => n = m))
\end{code}

Obviously, we can only construct an inhabitant for $isM$ $m$ $n$ if $n = m$. 

\subsubsection{Provided Atomic Predicates}

The approach for constructing atomic predicates described in the previous section can just as well be employed to define properties of other types. In our case, it makes most sense to define preconditions to be of the type $Predicate$ $FSTree$ (i.e. a script's precondition ranges over the state of the filesystem).  

Atomic predicates to specify the following properties are provided: 

\begin{itemize}
\item 
Whether a given path exists in the filesystem at all 

\item
If a path exists, whether the node it points to is of a certain type (i.e. \textit{File} or \textit{Directory}) 

\item 
If a path exists, whether the current user has certain permissions on the node that the path points to. 
\end{itemize}

The former two are quite easily specified once we have a datatype in place that holds proofs that a given path exists in a filesystem. For this datatype, we draw inspiration from the $Elem$ datatype, which is a witness to the fact that a certain element can be found in a list. The resulting datatype is defined as follows: 

\begin{code}
data FSElem : Path -> FSTree -> Type where 
  HereDir  : FSElem  (DirPath []) 
                     (FSNode x xs)
  HereFile : (n1 = n2) -> FSElem  (FilePath [] n1) 
                                  (FSLeaf (MkFileInfo n2 md)) 
  ThereDir : (fs : FSTree)  -> FSElem (DirPath xs) fs 
                            -> Elem fs ys -> (n : String) 
                            -> FSElem  (DirPath (n :: xs)) 
                                       (FSNode (MkFileInfo n md) ys)
  ThereFile : (fs : FSTree)  -> FSElem (FilePath xs x) fs 
                             -> Elem fs ys -> (n : String)
                             -> FSElem  (FilePath (n :: xs) x) 
                                        (FSNode (MkFileInfo n md) ys)
\end{code}

Though rather lengthy, the definition is actually quite straightforward. Any directory path with no components (i.e. "/") is part of a filesystem that has a node at the root. Any file with no components (i.e. "/filename.ext") is part of a filesystem that is just a leaf, provided the file in the leaf has the same name. 

In the recursive case, a path is in a filesystem if the first component is equal to the name of the file that is at the root node of the filesystem, there is a proof that the remainder of the path is part of some other filesystem, and there is a proof that said filesystem is one of the children of the root node. 



\subsection{Shallow Embedding Using Control.ST}

\subsection{HoareState}

\subsection{Free Monads}

\section{Conclusion}

\section{Future Work}

\begin{thebibliography}{99}
\bibitem{moore14}
Moore, S., Dimoulas, C., King, D., \& Chong, S. (2014, October). SHILL: A Secure Shell Scripting Language. In OSDI (pp. 183-199).

\bibitem{brady13}
Brady, E. (2013). Idris, a general-purpose dependently typed programming language: Design and implementation. Journal of Functional Programming, 23(5), 552-593.

\bibitem{saltzer74}
Saltzer, J. H. (1974). Protection and the control of information sharing in Multics. Communications of the ACM, 17(7), 388-402.

\bibitem{krohn05}
Krohn, M. N., Efstathopoulos, P., Frey, C., Kaashoek, M. F., Kohler, E., Mazieres, D., ... \& Ziegler, D. (2005, June). Make Least Privilege a Right (Not a Privilege). In HotOS.

\end{thebibliography}

\end{document}