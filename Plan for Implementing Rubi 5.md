## Plan for Implementing Rubi 5
The file **Rubi-5.m** is a *Mathematica* package that implements a functional *Rubi* 5 prototype. It shows the structure of the 42 Int*nnn* functions used to integrate algebraic functions. Each Int*nnn* function consists of a *single* deeply-nested, if-then-else control construct. Note that these functions do *not* rely on pattern matching making them easy to port of other CAS.

The Int*nnn* functions need to be compiled, either manually or automatically, from the *Rubi* 4 pattern matching rules so as to provide the same functionality. As an example, the functions Int111 and Int121 have been fully implemented in **Rubi-5.m**. They were manually compiled from the current *development* version of *Rubi* 4 source files **1.1.1 (a+b x)^m.nb** and **1.2.1 (a+b x+c x^2)^p.nb**, respectively. (Note these files have slightly different names in the current *distribution* version of *Rubi* 4.) The remaining 40 Int*nnn* functions are terminated with a Defer\[Int*nnn*] indicating they are place holders waiting to be compiled.

Comparing the 2 *Rubi* 4 source files with the functions Int111 and Int121 makes clear the near one-to-one correspondence between them. Thus it should be possible, though challenging, to implement a pattern-matching to if-then-else compiler to automate the process. Alternatively, the compilation could be turned into a crowdsourced project with each volunteer assigned an Int*nnn* function to manually compile.

Once all 42 Int*nnn* functions have been properly defined, the number of *Rubi* 4’s over 3000 algebraic function pattern matching rules for Int[u, x] will have been reduced to *Rubi* 5’s just 42 pattern matching rules. Porting *Rubi* 5 to a host CAS that provides even minimal pattern matching abilities should be capable of handling just 42 rules for Int[u, x].

Porting *Rubi* 5 to a CAS that does *not* support pattern matching will require the implementors define an Int[u, x] function that categorizes the arbitrary expression u and then calls the Int*nnn* function that services such expressions along with the appropriate arguments. Otherwise Int[u, x] should return the integral unevaluated.

That arbitrary expression categorization can be implemented using an if-then-else decision tree (of which I'm obviously a big fan) to define Int[u, x] as follows:
* Define a utility routine that returns an expression's type number: 1=linear, 2=quadratic, 3=cubic, 4=quartic, 5=binomial, 6=trinomial and 7=unknown.
* For Int[c f(x), x] where c is free of x, return c Int[f(x), x].
* For Int[f(x)+g(x), x], return Int[f(x), x] + Int[g(x), x].
* For Int[f(x)^m, x] where m is free of x, call the appropriate Int*nnn* function based on the type of f(x).
* For Int[f(x)^m g(x)^n ...] where m, n, ... are free of x, sort the list of base/degree pairs {{f(x),m}, {g(x),n}, ...} based on the type number of the bases. Then descend through a 42-leaf if-then-else decision tree based on the type of successive elements of the list and call the Int*nnn* function named at the leaf.
 
A disclaimer: The above description how to implement *Rubi* 5 glosses over numerous issues involved in compiling the 42 Int*nnn* functions and Int[u, x] itself into if-then-else decision trees.
