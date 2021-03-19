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

Finally, I'm keeping my focus squarely on perfecting *Rubi* 4 to my satisfaction *before* turning my attention to *Rubi* 5. So I invite others having the interest and expertise required to oversee the implementation of *Rubi* 5.
