# Rubi 5
## Rule-Based Integrator Built On An If-Then-Else Decision Tree
### Albert D. Rich, Applied Logician
#### 17 March 2021

It's been over two years since *Rubi* 4.16.1 was released. Although far from perfect, it is based on a fairly powerful, stable system of rules. The integration rules and associated test-suite on [*Rubi*'s website](https://rulebasedintegration.org/) are the most up-to-date, publicly available versions.

I’m in the midst of totally redesigning the decision tree implicit in *Rubi* 4's pattern matching rules used to integrate rational and algebraic functions (they account for about half the system's current 7800 rules). This redesign will
* greatly increase the class of expressions *Rubi* can integrate,
* provide simpler, more straight-forward derivations when single-stepping, and
* facilitate the compilation of *Rubi* 4’s pattern matching rules into *Rubi* 5’s if-then-else decision tree.

I will not release the next, and hopefully last, version of *Rubi* 4 until a coherent set of rules are *derived*, *debugged* and thoroughly *tested*. I cannot predict when that new version will be released, given the creative nature of the work. It all depends on where the math leads me.

Once this is accomplished, I can begin work in earnest on *Rubi* 5. That involves compiling *Rubi* 4's pattern matching rules into a deeply nested if-then-else decision tree. Thus far I have been doing this manually. Considering the tree has around 7800 leaves, it is extremely tedious, error-prone and time-consuming work.

Clearly this compilation should be automated. Conceptually that should be relatively fairly straight-forward to do, given the hierarchical nature of the decision tree implicit in *Rubi* 4's pattern matching rules.

Such a compiler would greatly facilitate the release of *Rubi* 5 with its numerous advantages. It will be relatively easy to port *Rubi* 5 to virtually any CAS supporting an if-then-else control construct. Also preliminary testing indicates selecting rules using an if-then-else tree rather than pattern matching means *Rubi* 5 will run almost 2-orders of magnitude faster than *Rubi* 4.

### Implementing Rubi 5

The file **Rubi-5.m** is a *Mathematica* package that implements a functional *Rubi* 5 prototype. It shows the structure of the 42 Int*nnn* functions used to integrate algebraic functions. Each Int*nnn* function consists of a *single* deeply-nested, if-then-else control construct. Note that these functions do *not* rely on pattern matching making them easy to port of other CAS.

The Int*nnn* functions need to be compiled, either manually or automatically, from the *Rubi* 4 pattern matching rules so as to provide the same functionality. As an example, the functions Int111 and Int121 have been fully implemented in **Rubi-5.m**. They were manually compiled from the current *development* version of *Rubi* 4 source files **1.1.1 (a+b x)^m.nb** and **1.2.1 (a+b x+c x^2)^p.nb**, respectively. (Note these files have slightly different names in the current *distribution* version of *Rubi* 4.)

The remaining 40 Int*nnn* are terminated with a Defer\[Int*nnn*] indicating they are place holders waiting to be compiled. Comparing the 2 *Rubi* 4 source files with the functions Int111 and Int121 makes clear the near one-to-one correspondence between them. Thus it should be possible, though challenging, to implement a pattern-matching to if-then-else compiler to automate the process.

Alternatively, the compilation could be turned into a crowdsourced project with volunteers assigned an Int*nnn* file to manually compile...

Again to be clear, I keeping my focus squarely on perfecting *Rubi* 4 to my satisfaction *before* turning my attention to *Rubi* 5. So I invite others having the interest and expertise required to honcho the implementation of *Rubi* 5.
