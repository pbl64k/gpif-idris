# Generic Programming with Indexed Functors in Idris

This is a partial translation of Agda code in A. Löh and J. P. Magalhães
*Generic Programming with Indexed Functors* to Idris. I have an interest in
getting recursion schemes for free, and as far as I know, *GPIF* is currently
state of the art (though the practicality of this particular approach is
somewhat debatable). Reading the paper was somewhat enlightening, but I
wanted to develop a better grasp of how all of this works. As I also wanted
to tinker with Idris, I thought that translating the companion code would be
an excellent project to achieve both goals. (And that's exactly how it worked
out for me.)

While the implementation is probably of little practical interest, I wanted
to share my insights. To that end, the code is commented quite extensively.
(This is not a `.lidr`, though, as I am a little averse to all the
greater-than signs.)

This is only a partial translation, covering the material roughly up to and
including 2.6. The sketchy even-odd list example at the very end is similar
in design and purpose to the AST example in 2.7, but it is substantially
simpler. The rose tree example in *GPIF* seemed overcomplicated to me without
offering any advantages, so I used a simpler version both for the definition
and for concrete instantiations of map and fold. I also included a recursive
definition of booleans just for laughs.

I may eventually translate the material up to the end of section 2, and, with
somewhat lower likelihood, section 3, but I have no desire to tackle sections
4 and 5.

Idris is a fun language to use, but it has its fair share of warts (at least
some of which can be explained by its pre-release status). Totality checker
is wonky, and attempts to subtly nudge it towards admitting totality often
seem to result in seriously cryptic type errors. Type errors, in general, are
*very* cryptic (more so than Haskell's type errors seemed to be when I was
just starting with it), and while some of that definitely can be attributed
to the power of Idris' type system, error reporting in general seems to be
quite unsatisfactory. (Failure to unify what looks like two instances of the
same type may be explainable, but it is seriously befuddling to newcomers,
and pinpointing the errors is unreasonably hard.) In addition, Idris seems to
be much worse than Agda at figuring out the implicit arguments to function
application. The Idris code is annotated much more thoroughly because of
that.

See also a version of the same in Haskell using DataKinds:

https://github.com/pbl64k/gpif-datakinds

Additional reading:

Conor McBride, *Clowns to the Left of me, Jokers to the Right: Dissecting
Data Structures*

Conor McBride, *Slicing It: Indexed Containers in Haskell (Programming Pearl)*

Edward A. Kmett, Haskell library `recursion-schemes`

Fritz Ruehr, *The Evolution of a Haskell Programmer*

