# Experimentation Project: Trustworthy shell scripts using dependent types in Idris

When executing shell scripts obtained from a third party, there is no way of knowing that such a script won't cause damage to your computer without examining the actual contents of the script. 

[Shill](http://shill.seas.harvard.edu/shill-osdi-2014.pdf) is a shell scripting language designed to address this problem, which requires scripts to present a so-called *contract*, which specifies which resources (and what level of access to them) the script needs. The script is then executed in a sandbox that ensures that the script does not overstep the permissions defined in its contract. 

This design implies that contracts are only checked dynamically, even though it is to some extent possible to verify whether a script violates its contract by performing static checks. 

## Goal

The goal of this project is to implement a subset of Bash as an EDSL in [Idris](https://www.idris-lang.org/), utilizing Idris' dependent type system to provide more guarantees about the resources a script will use during its lifetime. 

### Description

The goal of this project can be roughly divided into two parts:

* Statically ensure that scripts do not require permissions beyond what's defined in their contract. 
* Prevent scripts from executing when they require permissions beyond what is implied by the ambient permissions of the user that runs the script. This will need to be able to account for commands that may change the ambient permission (```su```/```sudo```) or commands that change the permissions of a file/directory (```chmod```/```chown```). 

Furthermore it is important to recognise that all but a few commands commonly used from within a Bash shell are simply binaries that reside in one of de directories specified in ```$PATH```, meaning that there is no real difference between a call to ```ls``` and a call to an arbitrary executable (at least from a technical point of view). Hence it might be worthwile to come up with some kind of abstraction, and define the commonly used commands in Bash in terms of this abstraction.

Such an approach may also allow for automated testing of the contracts associated with commands in a sandbox environment. 

### Minimal viable product

A library which allows for definition of shell scripts that use a small amount of commands, for which it is statically checked that the permissions specified in the contract are respected, as well as checks that rule out certain other types of problems (e.g. the user running a script doesn't have the required permissions to do so). 

## Getting Started

These instructions will get you a copy of the project up and running on your local machine for development and testing purposes. 

### Prerequisites

Running the project requires [Idris](https://www.idris-lang.org/) to be installed on the target computer. Installation instructions for all mainstream operating systems can be found [here](https://github.com/idris-lang/Idris-dev/wiki/Installation-Instructions). 

### Installing

**TODO**

## Relevant Literature

* [Idris, a general-purpose dependently typed programming language: Design and implementation](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/idris-a-generalpurpose-dependently-typed-programming-language-design-and-implementation/418409138B4452969AC0736DB0A2C238)
* [Programming and reasoning with algebraic effects and dependent types](https://dl.acm.org/citation.cfm?id=2500581)
* [SHILL: A Secure Shell Scripting Language](http://shill.seas.harvard.edu/shill-osdi-2014.pdf)
* [The Semantics of Version Control](https://dl.acm.org/citation.cfm?id=2661137)
* [State Machines All The Way Down](https://www.idris-lang.org/drafts/sms.pdf)





