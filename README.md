# SMaSH
SMaSH (Simplify Massive Spinor Helicity) is a Mathematica package to do massive spinor helicity computations.


# Features
1. Explicit handling of massive little group indices
2. Contraction of spinor and little group indices
3. Spinor derivatives, massive & massless helicity scaling operators
4. Implementation of RAMBO algorithm and generation of random numerical kinematics for any n point scattering
5. Discrete C, P, T transformations
6. Three point amplitudes for any masses and spins
7. Higher spin propagators
8. Mandelstam simplifications
9. Finding contact terms and manifesting gauge invariance


# Download
https://github.com/aakash-kmr/SMaSH/archive/refs/heads/main.zip


# How to install

The package can be installed using any one of the following ways.

1. Download the .zip file from the and extract it in any folder. After extracting, open a Mathematica notebook and follow these steps 

            "File"  ->  "Install..."  ->  Choose "Packages" from "Type of Item to Install"  ->  Choose "From File..." from "Source"   ->   Choose either "Install for this user only" or "Install for all users"   ->   "OK"   ->    Run "<<SMaSH`"

2. To manually install the package, first download the .zip file. Get the user base directory by running "\$UserBaseDirectory" and then extract the .zip file in the folder "\$UserBaseDirectory\Applications". Then load the package by running "<<SMaSH`".

3. To load the package for a particular notebook, download the .zip file and extract it in any folder. After extracting, open the Mathematica notebook and paste the address of the folder within the command SetDirectory. For example, if the package is extracted in the folder "MyPackages" whose complete address is "C:Users\HP\Downloads\MyPackages" then simply run "SetDirectory["C:Users\HP\Downloads\MyPackages"]" and then run "<<SMaSH`".


# Documentation
[arXiv paper](https://arxiv.org/pdf/2606.27928)

# Citation
If any part of this package have been useful to you, please cite us. The citation texts can be downloaded from [inspirehep](https://inspirehep.net/literature/3174196). 

# License
GNU GENERAL PUBLIC LICENSE
                       Version 3, 29 June 2007

 Copyright (C) 2007 Free Software Foundation, Inc. <https://fsf.org/>
 Everyone is permitted to copy and distribute verbatim copies of this license document, but changing it is not allowed.

 # Note
Please add an issue [here](https://github.com/aakash-kmr/SMaSH/issues) if you have any issue with the code, or you can raise a [pull request](https://github.com/aakash-kmr/SMaSH/pulls) also if you fix anything. For any kind of comments or discussion, please use the [Discussion](https://github.com/aakash-kmr/SMaSH/discussions) section. You can also email us at aakash.kumar.physics@gmail.com or rahulshaw.phy@gmail.com or rudra19@iiserb.ac.in
