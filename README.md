# CoqFFJ
Feature Featherweight Java is a minimimum core calculus for Java formalized in [this paper](https://github.com/hephaestus-pl/coqffj/blob/master/docs/ffjtech.pdf)

CoqFFJ is a mechanization of the standard theorems for type safety, i.e. progress and preservation, using coq. Built upon [CoqFJ](https://github.com/hephaestus-pl/coqfj) Release 1.1.

To compile the code, simply run ```make``` at the root folder.

You can also generate the makefile from scratch running ```coq_makefile -f _CoqProject -o makefile```

If you use CoqIDE, make sure to enable Project File options at ```Edit -> Preferences -> Project Project file options are "append to arguments"```.

And ```Default name for project file _CoqProject```
