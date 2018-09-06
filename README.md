# Experimentation Project: Trustworthy shell scripts using dependend types in Idris

## Motivation 

When executing shell scripts obtained from a third party, there is no way of knowing that such a script won't cause damage to your computer without examining the actual contents of the script. 

[Shill](http://shill.seas.harvard.edu/shill-osdi-2014.pdf) is a shell scripting language designed to address this problem, which requires scripts to present a so-called *contract*, which specifies which resources (and what level of access to them) the script needs. The script is then executed in a sandbox that ensures that the script does not overstep the permissions defined in its contract. 

This design implies that contracts are only checked dynamically, even though it is to some extent possible to verify whether a script violates its contract by performing static checks. 

## Goal

The goal of this project is to implement a subset of Bash as an EDSL in [Idris](https://www.idris-lang.org/), utilizing Idris' dependend type system to provide more guarantees about the resources a script will use during its lifetime. 


