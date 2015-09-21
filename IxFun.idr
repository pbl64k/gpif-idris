
%default total

record Isomorphic a b where
    constructor MkIso
    from : a -> b
    to : b -> a
    iso1 : (x : a) -> to (from x) = x
    iso2 : (x : b) -> from (to x) = x

{-
`Isomorphic a b' witnesses the isomorphism between two types, and allows us
to convert the values of one type to another and vice versa.

Note that the record is supposed to include proofs that `from' and `to' are
each other's inverses; in practice, I chicken out and just postulate the
"truthiness" of that in all except the simplest of cases.

It might sound like a good idea to use implicit conversions instead, but that
doesn't seem to work well in practice.
-}



IndexedType : Type -> Type
IndexedType index = index -> Type

{-
`IndexedType a' is essentially a family of types, such that every value of
`a' is mapped to a type. E.g., `const Bool' would be a fine example of
`IndexedType ()', which is isomorphic to "ordinary" types, as unit type has
a single inhabitant -- functions of type `() -> a' are isomorphic to values
of type `a', if not necessarily completely interchangeable in practice, and
we're just dealing with functions evaluating to types here.

`IndexedType Bool' would be inhabited by "families" of two types, a random
example being:
-}

someIndexedType : IndexedType Bool
someIndexedType False = Nat
someIndexedType True = Nat -> Nat



{-
Here indexed types are typically built out of units, sums and products, e.g.
`Either () ()' (in type theorists' lingo, "1 + 1") would be isomorphic to
`Bool', its two inhabitants being `Left ()' and `Right ()'. Just to
illustrate the stuff introduced so far:
-}

isoBoolTwo : Isomorphic Bool (Either () ())
isoBoolTwo = MkIso from to iso1 iso2
    where
        from : Bool -> Either () ()
        from False = Left ()
        from True = Right ()
        to : Either () () -> Bool
        to (Left ()) = False
        to (Right ()) = True
        iso1 : (x : Bool) -> to (from x) = x
        iso1 False = Refl
        iso1 True = Refl
        iso2 : (x : Either () ()) -> from (to x) = x
        iso2 (Left ()) = Refl
        iso2 (Right ()) = Refl

{-
Note this has little bearing on what's to follow, being just another random
example.
-}



union : IndexedType firstIndex -> IndexedType secondIndex ->
        IndexedType (Either firstIndex secondIndex)
union f g = either f g

{-
For convenience, `union' produces a "sum" of indexed types, that is:
-}

anotherIndexedType : IndexedType (Either () Bool)
anotherIndexedType = union (const Bool) someIndexedType

{-
...which would map `Left ()' to `Bool', `Right False' to `Nat' and
`Right True' to `Nat -> Nat':
-}

anotherIndexedTypeExample1 : anotherIndexedType (Left ()) = Bool
anotherIndexedTypeExample1 = Refl

anotherIndexedTypeExample2 : anotherIndexedType (Right False) = Nat
anotherIndexedTypeExample2 = Refl

anotherIndexedTypeExample3 : anotherIndexedType (Right True) = (Nat -> Nat)
anotherIndexedTypeExample3 = Refl



arrow : {index : Type} -> IndexedType index -> IndexedType index -> Type
arrow {index = index} ixTypeSrc ixTypeTgt =
        (inp : index) -> ixTypeSrc inp -> ixTypeTgt inp

{-
`arrow' produces the type or "generalized functions" between two indexed
types using the same indices.

Such arrows are parametrized by a given index `inp', and when applied to it
produce an orinary function between the two types yielded by the
corresponding indexed types when applied to the same `inp'.

In the trivial case of `index' being a unit type, such arrows are isomorphic
to the ordinary functions between the types "embedded" in the indexed types.
A random example:
-}

dumbIndexedType1 : IndexedType Bool
dumbIndexedType1 False = ()
dumbIndexedType1 True = Bool

dumbIndexedType2 : IndexedType Bool
dumbIndexedType2 False = Bool
dumbIndexedType2 True = ()

myMorphism : dumbIndexedType1 `arrow` dumbIndexedType2
myMorphism False = \() => True
myMorphism True = \_ => ()

{-
Depending on which index we want to apply it to -- `True' or `False' --
`myMorphism' reduces either to a function from unit type to `Bool' or to a
function from `Bool' to `()'.
-}



split : r `arrow` u -> s `arrow` v -> union r s `arrow` union u v
split f _ (Left x) = f x
split _ f (Right x) = f x

{-
Produces left outputs from left inputs using the first arrow, and right
outputs from right inputs using the second arrow. Note that this is defined
for our "arrows" rather than for ordinary functions.
-}



fanout : (a -> b) -> (a -> c) -> a -> (b, c)
fanout f g x = (f x, g x)

{-
Produces a pair resulting from application of both given functions to our
input. Unlike `split', this is for ordinary functions rather than our arrows
operating on indexed types.
-}



lift : {index : Type} -> (a -> b) ->
        arrow {index = index} (const a) (const b)
lift f _ x = f x

{-
Another utility combinator -- this lifts a function to an arrow on constant
indexed types (that is, those that map to the same type regardless of the
index).
-}



idArrow : {index : Type} -> {type : IndexedType index} -> type `arrow` type
idArrow _ = id

{-
The identity function lifted to indexed types.
-}



composeArrow : a `arrow` b -> b `arrow` c -> a `arrow` c
composeArrow f g index = g index . f index

{-
We don't really need this, but the arrows compose nicely.
-}



IndexedFunctor : Type -> Type -> Type
IndexedFunctor inputIndex outputIndex =
        IndexedType inputIndex -> IndexedType outputIndex

{-
Indexed functors map indexed types to indexed types. E.g.,
`IndexedFunctor () Bool' should map all types indexed by unit to types
indexed by `Bool'. Note that `IndexedFunctor () Bool' is just:

IndexedType () -> IndexedType Bool

Which, in turn, can be reduced to:

(() -> Type) -> Bool -> Type

Can we implement a function like that? Well, sure...
-}

randomFunctor : IndexedFunctor () Bool
randomFunctor ixType = const (ixType ())



{-
Now what in the seven hells does any of that have to do with algebraic data
types, maps and folds?.. Fasten your seat belts.
-}

mutual
    data IxFun : (inputIndex : Type) -> (outputIndex : Type) -> Type where
        Zero : IxFun inputIndex outputIndex
        One : IxFun inputIndex outputIndex
        Sum : IxFun inputIndex outputIndex -> IxFun inputIndex outputIndex ->
                IxFun inputIndex outputIndex
        Product : IxFun inputIndex outputIndex ->
                IxFun inputIndex outputIndex -> IxFun inputIndex outputIndex
        Composition : {intermediateIndex : Type} ->
                IxFun intermediateIndex outputIndex ->
                IxFun inputIndex intermediateIndex ->
                IxFun inputIndex outputIndex
        Iso : (representable : IxFun inputIndex outputIndex) ->
                (isomorphicFunctor : IndexedFunctor inputIndex outputIndex) ->
                        ((inputType : IndexedType inputIndex) -> (out : outputIndex) ->
                        Isomorphic (isomorphicFunctor inputType out) (interp representable inputType out)) ->
                IxFun inputIndex outputIndex
        Fix : IxFun (Either inputIndex outputIndex) outputIndex -> IxFun inputIndex outputIndex
        Input : inputIndex -> IxFun inputIndex outputIndex
    
{-
First, we build an encoding using the universe pattern. We cannot pattern
match on types, and in any case, there are limits to what can be done in this
framework.
-}

    interp : IxFun inputIndex outputIndex -> IndexedFunctor inputIndex outputIndex
    interp Zero _ _ = Void
    interp One _ _ = ()
    interp (Sum f g) inputType out =
            Either (interp f inputType out) (interp g inputType out)
    interp (Product f g) inputType out =
            (interp f inputType out, interp g inputType out)
    interp (Composition f g) inputType out =
            (interp f . interp g) inputType out
    interp (Iso _ hostFunctor _) inputType out = hostFunctor inputType out
    interp (Fix functor) inputType out = Mu functor inputType out
    interp (Input inp) inputType _ = inputType inp

{-
The codes are useless on their own, so we need an interpretation function
that will build actual indexed functors from the provided codes. Much of this
stuff is straightforward and unsurprising:

1. We have the basic building blocks in form of `Zero' and `One', which
   simply map everything to void and unit types correspondingly.

2. Sum, product and composition are also as one would expect -- we can lift
   pairs of compatible indexed functors to functors that yield sums or
   products of types, and we can compose indexed functors as well (as long as
   the indices involved are compatible).

3. `Iso' is a neat trick that will later allow us to obtain `imap' that works
   almost transparently for types that are isomorphic to those directly
   representable in the universe. This doesn't work as neatly for
   catamorphisms and the rest of the zoo, but it's still nice to have.

4. `Fix' employs `Mu' below, which is similar to the definition of `Mu' that
   allows us to obtain recursive data structures from functors in other
   settings. This is the key piece, and it sheds a lot of light onto what's
   going here with the whole indexed functors thing.
-}

    data Mu : (baseFunctorRepr : IxFun (Either inputIndex outputIndex) outputIndex) ->
            (inputType : IndexedType inputIndex) -> (out : outputIndex) -> Type where
        In : interp baseFunctorRepr (union inputType (Mu baseFunctorRepr inputType)) outputIndex ->
                Mu baseFunctorRepr inputType outputIndex

{-
Recall a straightforward `Mu' which takes a functor (in Haskell sense of the
word) and produces a recursive data type without any parameters. This can be
generalized to `Mu2' which takes a bifunctor and produces a recursive data
type with one parameter (which also happens to be a "functor"). In both
cases, one of the parameters of the base functor is used to plug the functor
back into itself. There's no simple way to generalize this to arbitrary
arities without having a sufficiently powerful type system. But the power of
dependent types is enough to do precisely that!

Indexed functors really are generalizations of covariant functors and
bifunctors. An "ordinary" functor takes a single type as an argument. An
indexed functor takes an indexed type -- which can represent arbitrarily many
types, and thus arbitrarily many arguments. (We can also produce arbitrarily
many types with our functors, but more on that later.)

So this particular definition of `Mu' uses a simple encoding -- argument
types resulting from indices tagged as `Left' are to be left untouched, while
those tagged as `Right' are to be plugged back into the functor recursively.
Thus, `Mu' takes a base indexed functor mapping types indexed with
`Either a b' to types indexed with `b' and produces a functor mapping types
indexed with `a' to types indexed by with `b'.

There is a section with examples below, which should be able to shed further
light on how all of this works.
-}



baseFunctor :
        {functor : IxFun (Either inputIndex outputIndex) outputIndex} ->
        Mu functor _ _ -> IxFun (Either inputIndex outputIndex) outputIndex
baseFunctor {functor = functor} _ = functor

{-
Using the foo-morphisms below for a given data type requires the knowledge of
the type's base functor (as it determines the type of the algrebras and
coalgebras involved). I could just spell it out (it's actually easier that
way in practice!), but it's also possible to pull it out of the `Mu'
directly.
-}



imap : {inputIndex : Type} -> {outputIndex : Type} ->
        {r : IndexedType inputIndex} -> {s : IndexedType inputIndex} ->
        (functorRepr : IxFun inputIndex outputIndex) ->
        r `arrow` s ->
        interp functorRepr r `arrow` interp functorRepr s
imap One _ _ () = ()
imap (Sum g _) f out (Left x) = Left (imap g f out x)
imap (Sum _ g) f out (Right x) = Right (imap g f out x)
imap (Product g h) f out (x, y) = (imap g f out x, imap h f out y)
imap {r = r} {s = s} (Composition g h) f out x =
        imap {r = interp h r} {s = interp h s} g (imap h f) out x
imap {r = r} {s = s} (Iso repr host isomorphism) f out x =
        to iso2 (imap repr f out (from iso1 x))
    where
        iso1 : Isomorphic (host r out) (interp repr r out)
        iso1 = isomorphism r out
        iso2 : Isomorphic (host s out) (interp repr s out)
        iso2 = isomorphism s out
imap {r = r} {s = s} (Fix g) f out (In x) =
        In (imap {r = union r (Mu g r)} {s = union s (Mu g s)} g f' out x)
    where
        %assert_total
        f' : union r (Mu g r) `arrow` union s (Mu g s)
        f' = split f (imap (Fix g) f)
imap (Input inp) f _ x = f inp x

{-
This is arguably the piece de resistance here. `imap' generalizes ordinary
functorial `fmap' (and bifunctorial `bimap') working for functors taking any
numbers of parameters -- as long as those are representable in the universe
encoding above! Instead of lifting functions (or pairs of functions) we're
lifting "arrows" defined above, which are really just collections of
functions working for all the indices involved. The implementation is
straightforward, and the biggest challenge here is getting the implicit
parameters to recursive calls right. Unfortunately, unlike Agda used in the
GPIF paper, Idris doesn't seem capable of doing that on it's own (or I just
don't know how to cook it right).

Note that `imap' is actually total, as we cannot build infinite data
structures in this framework without subverting the totality checker.
Unfortunately, I know of no easy way to demonstrate that to the checker, so I
resorted to simply asserting totality.
-}



{-
Catamorphisms are folds.
-}

cata : {inputIndex : Type} -> {outputIndex : Type} ->
        {r : IndexedType inputIndex} -> {s : IndexedType outputIndex} ->
        (baseFunctorRepr : IxFun (Either inputIndex outputIndex) outputIndex) ->
        interp baseFunctorRepr (union r s) `arrow` s ->
        interp (Fix baseFunctorRepr) r `arrow` s
cata {inputIndex = inputIndex} {outputIndex = outputIndex} {r = r} {s = s}
        baseFunctorRepr algebra out (In x) =
        algebra out (imap {r = r'} {s = s'} baseFunctorRepr f out x)
    where
        r' : IndexedType (Either inputIndex outputIndex)
        r' = union r (Mu baseFunctorRepr r)
        s' : IndexedType (Either inputIndex outputIndex)
        s' = union r s
        %assert_total
        f : r' `arrow` s'
        f = split (idArrow {type = r})
                (cata {r = r} {s = s} baseFunctorRepr algebra)

{-
This is just a very general version of:

cata : Functor f => (f a -> a) -> Fix f -> a

Further complicated by the fact that it only works for fixed points of types
representable in the universe. The point is exactly the same, though, given
an algebra for the base functor of a recursive data type, we can lift it to
collapse the recursive structure of data while performing some computations.

The two explicit parameters are the representation of the base functor
(needed to give the right type to the following parameters), and the algebra,
which in this case is an arrow with the freaky type. (The point is still the
same, though, -- it takes a functor with some of the parameters marked as
"recursive holes", and produces a single value of the same indexed type.)

`imap' is an important part of implementation, as it is used for a recursive
call on all the recursive indices, while leaving the "input" indices
untouched to feed the associated data directly to `algebra'.

Unfortunately, once again I see no easy way to prove that this is total,
despite the fact that it seems really obvious.
-}



{-
Anamorphisms are unfolds.

Note that we can't really guarantee termination here. Unfortunately, codata
is outside of the universe, so there doesn't seem to be a lot to do here in
a principled fashion.
-}

partial
ana : {inputIndex : Type} -> {outputIndex : Type} ->
        {r : IndexedType inputIndex} -> {s : IndexedType outputIndex} ->
        (baseFunctorRepr : IxFun (Either inputIndex outputIndex) outputIndex) ->
        s `arrow` interp baseFunctorRepr (union r s) ->
        s `arrow` interp (Fix baseFunctorRepr) r
ana {inputIndex = inputIndex} {outputIndex = outputIndex} {r = r} {s = s}
        baseFunctorRepr coalgebra out x =
        In (imap {r = r'} {s = s'} baseFunctorRepr f out (coalgebra out x))
    where
        r' : IndexedType (Either inputIndex outputIndex)
        r' = union r s
        s' : IndexedType (Either inputIndex outputIndex)
        s' = union r (Mu baseFunctorRepr r)
        partial
        f : r' `arrow` s'
        f = split (idArrow {type = r})
                (ana {r = r} {s = s} baseFunctorRepr coalgebra)

{-
Implementation-wise, this is the perfect dual to `cata' and is trivial to get
right by reversing the arrows.
-}



{-
Hylomorphisms are equivalent to a composition of an unfold with a fold. Since
unfolds are involved, this is also partial.
-}

partial
hylo : {inputIndex : Type} -> {outputIndex : Type} ->
        {r : IndexedType inputIndex} -> {s : IndexedType outputIndex} ->
        {t : IndexedType outputIndex} ->
        (baseFunctorRepr : IxFun (Either inputIndex outputIndex) outputIndex) ->
        interp baseFunctorRepr (union r t) `arrow` t ->
        s `arrow` interp baseFunctorRepr (union r s) ->
        s `arrow` t
hylo {inputIndex = inputIndex} {outputIndex = outputIndex}
        {r = r} {s = s} {t = t} baseFunctorRepr algebra coalgebra out x =
        algebra out (imap {r = r'} {s = s'} baseFunctorRepr f out (coalgebra out x))
    where
        r' : IndexedType (Either inputIndex outputIndex)
        r' = union r s
        s' : IndexedType (Either inputIndex outputIndex)
        s' = union r t
        partial
        f : r' `arrow` s'
        f = split (idArrow {type = r})
                (hylo {r = r} {s = s} {t = t} baseFunctorRepr algebra coalgebra)

{-
This is more efficient than composing `ana' and `cata', but otherwise
equivalent.
-}



{-
Paramorphisms are generalized folds, commonly described as "using their value
and keeping it too."
-}

para : {inputIndex : Type} -> {outputIndex : Type} ->
        {r : IndexedType inputIndex} -> {s : IndexedType outputIndex} ->
        (baseFunctorRepr : IxFun (Either inputIndex outputIndex) outputIndex) ->
        interp baseFunctorRepr (union r (\o => Pair (s o) (interp (Fix baseFunctorRepr) r o))) `arrow` s ->
        interp (Fix baseFunctorRepr) r `arrow` s
para {inputIndex = inputIndex} {outputIndex = outputIndex} {r = r} {s = s}
        baseFunctorRepr algebra out (In x) =
        algebra out (imap {r = r'} {s = s'} baseFunctorRepr f out x)
    where
        r' : IndexedType (Either inputIndex outputIndex)
        r' = union r (Mu baseFunctorRepr r)
        s' : IndexedType (Either inputIndex outputIndex)
        s' = union r (\o => Pair (s o) (interp (Fix baseFunctorRepr) r o))
        %assert_total
        f : r' `arrow` s'
        f = split (idArrow {type = r})
                (\ix => fanout (para {r = r} {s = s} baseFunctorRepr algebra ix) id)

{-
Metamorphisms and apomorphisms are left as an exercise for the reader. Since
they're dual to hylomorphisms and paramorphisms correspondingly, the
derivation should be "easy." (Cf. `cata' and `ana'.)
-}



{-
Well, and now let's try to take off with all that stuff...
-}



{-
Booleans.
-}

CodeBool : IxFun Void ()
CodeBool = Sum One One

{-
Bool takes no parameters (which is why the input index is `Void') and is
isomorphic to the sum of two unit types, as I mentioned before.
-}

fromBool : Bool -> interp CodeBool r o
fromBool False = Left ()
fromBool True = Right ()

toBool : interp CodeBool r o -> Bool
toBool (Left ()) = False
toBool (Right ()) = True

isoBool1 : (b : Bool) -> toBool (fromBool b) = b
isoBool1 False = Refl
isoBool1 True = Refl

isoBool2 : (b : interp CodeBool r o) -> fromBool (toBool b) = b
isoBool2 (Left ()) = Refl
isoBool2 (Right ()) = Refl

isoBool : (r : IndexedType Void) -> (o : ()) ->
        Isomorphic Bool (interp CodeBool r o)
isoBool r o =
        MkIso
            (fromBool {r = r} {o = o})
            (toBool {r = r} {o = o})
            isoBool1
            (isoBool2 {r = r} {o = o})

IsoBool : IxFun Void ()
IsoBool = Iso CodeBool (\_, _ => Bool) isoBool

{-
...but all of that is fairly uninspiring. Can we do something more
interesting?

Well, we can treat `Bool' as a recursive type. Wait, what?
-}

CodeRecBoolFunctor : IxFun (Either Void ()) ()
CodeRecBoolFunctor = Sum One One

CodeRecBool : IxFun Void ()
CodeRecBool = Fix CodeRecBoolFunctor

{-
Bwahaha!
-}

fromRecBool : Bool -> interp CodeRecBool r o
fromRecBool False = In (Left ())
fromRecBool True = In (Right ())

toRecBool : interp CodeRecBool r o -> Bool
toRecBool (In (Left ())) = False
toRecBool (In (Right ())) = True

isoRecBool : (r : IndexedType Void) -> (o : ()) ->
        Isomorphic Bool (interp CodeRecBool r o)
isoRecBool r o =
        MkIso
            (fromRecBool {r = r} {o = o})
            (toRecBool {r = r} {o = o})
            (\_ => believe_me ())
            (\_ => believe_me ())

{-
I'm omitting the isomorphism proof, because, seriously, it's the same as for
the sane `Bool' above.
-}

IsoRecBool : IxFun Void ()
IsoRecBool = Iso CodeRecBool (\_, _ => Bool) isoRecBool

{-
And now we can use `cata'... on `Bool'!
-}

foldBool : {a : Type} -> Bool -> Lazy a -> Lazy a -> a
foldBool cond xThen xElse = cata {r = const ()} {s = const a}
        CodeRecBoolFunctor algebra () (fromRecBool cond)
    where
        algebra : interp CodeRecBoolFunctor (union (const ()) (const a)) `arrow` const a
        algebra = \_ => either (const xElse) (const xThen)

{-
Now why would we do something like that? The only answer I have to this
question is, "Because we can!"

Other than that, it's just a *really* perverse way to pattern match on
`Bool'.
-}

foldBoolExample1 : foldBool True 1 2 = 1
foldBoolExample1 = Refl

foldBoolExample2 : foldBool False 1 2 = 2
foldBoolExample2 = Refl



{-
Nats.
-}

{-
Now let's try to do something with natural numbers.
-}

CodeNatsFunctor : IxFun (Either Void ()) ()
CodeNatsFunctor = Sum One (Input (Right ()))

{-
I find it strangely funny that the base functor for nats is isomorphic to
`Maybe', but I can't really explain why.

Of course, we could have coded `Maybe' as a "recursive" data type as with
booleans above, but I think that it would have been too much of a good thing.
-}

CodeNats : IxFun Void ()
CodeNats = Fix CodeNatsFunctor

fromNats : Nat -> interp CodeNats r o
fromNats Z = In (Left ())
fromNats (S n) = In (Right (fromNats n))

%assert_total
toNats : interp CodeNats r o -> Nat
toNats (In (Left ())) = Z
toNats {r = r} {o = ()} (In (Right n)) = S (toNats n) --(assert_smaller (In (Right n)) n))

{-
It should be trivial to prove totality here by using `assert_smaller' (for
that matter, Idris really should be capable of recognizing that the argument
to recursive call is strictly decreasing here!) -- but it isn't. All my
attempts to do so ran into a wall of seriously cryptic error messages and
weird phenomena such as the function apparently being accepted as total, but
the factorial examples below starting to fail, apparently due to
non-reduction in types.
-}

isoNats : (r : IndexedType Void) -> (o : ()) ->
        Isomorphic Nat (interp CodeNats r o)
isoNats r o =
        MkIso
            (fromNats {r = r} {o = o})
            (toNats {r = r} {o = o})
            (\_ => believe_me ())
            (\_ => believe_me ())

IsoNats : IxFun Void ()
IsoNats = Iso CodeNats (\_, _ => Nat) isoNats

{-
And now, in the time-honored tradition of *The Evolution of a Haskell
Programmer*, let's tackle the age old problem of implementing the factorial
in the most perverse fashion possible.
-}

paraNats : a -> (a -> Nat -> a) -> Nat -> a
paraNats zero suc n =
        para {r = r'} {s = s'} CodeNatsFunctor algebra () (fromNats n)
    where
        r' : IndexedType Void
        r' = const ()
        s' : IndexedType ()
        s' = const a
        algebra : interp CodeNatsFunctor (Main.union r' (\o => Pair (s' o) (interp (Fix CodeNatsFunctor) r' o))) `arrow` s'
        algebra = \() => either (const zero) (\(x, n') => suc x (succ (toNats n')))

factorial : Nat -> Nat
factorial = paraNats 1 (*)

{-
Whee!
-}

factorialExample1 : factorial 0 = 1
factorialExample1 = Refl

factorialExample2 : factorial 5 = 120
factorialExample2 = Refl



{-
Cons-cell lists.
-}

{-
Now let's do the lists. Everything should be fairly rote by now.
-}

CodeListFunctor : IxFun (Either () ()) ()
CodeListFunctor = Sum One (Product (Input (Left ())) (Input (Right ())))

{-
Unlike nats and booleans, lists are polymorphic, so we need two arguments --
one to specify the type of the elements, and one to plug the base functor
back into itself.
-}

CodeList : IxFun () ()
CodeList = Fix CodeListFunctor

fromList : {r : IndexedType ()} -> {o : ()} -> List (r o) -> interp CodeList r o
fromList [] = In (Left ())
fromList {o = ()} (x :: xs) = In (Right (x, fromList xs))

%assert_total
toList : {r : IndexedType ()} -> {o : ()} -> interp CodeList r o -> List (r o)
toList (In (Left ())) = []
toList {o = ()} (In (Right (x, xs))) = x :: toList xs

{-
Same troubles as with `toNats' above here.
-}

isoList : (r : IndexedType ()) -> (o : ()) ->
        Isomorphic (List (r o)) (interp CodeList r o)
isoList r o =
        MkIso
            (fromList {r = r} {o = o})
            (toList {r = r} {o = o})
            (\_ => believe_me ())
            (\_ => believe_me ())

{-
I'm skipping the proof again, if you're curious, you can refer the GPIF,
which does contain a surprisingly unwieldy proof.
-}

IsoList : IxFun () ()
IsoList = Iso CodeList (\f, t => List (f t)) isoList

{-
Having established the isomorphism between `List's and indexed functor
represented by `CodeList', we can now instantiate concrete map and fold for
lists.
-}

mapList : {a : Type} -> {b : Type} -> (a -> b) -> (List a -> List b)
mapList {a = a} {b = b} f =
        imap {r = const a} {s = const b} IsoList (lift f) ()

mapListExample : mapList succ [1, 2, 3] = [2, 3, 4]
mapListExample = Refl

foldList : {a : Type} -> {r : Type} -> (a -> r -> r) -> r -> List a -> r
foldList {a = a} {r = r} c n xs =
        cata {r = const a} {s = const r}
                (baseFunctor (fromList {r = const a} {o = ()} xs)) phi ()
                (fromList xs)
    where
        phi : () -> Either () (a, r) -> r
        phi = \_ => (either (const n) (uncurry c))

{-
At this point it's probably worth noting that this is less practical than
aesthetically pleasing. While the concept is beautiful, the unnatural
contortions that we need to go through to actually use generic catamorphisms
make the idea unappealing in practice. 
-}

foldListExample : foldList (+) 0 [1, 2, 3] = 6
foldListExample = Refl

lengthList : List a -> Nat
lengthList = foldList (const succ) 0

lengthListExample : lengthList [1, 2, 1, 2, 1] = 5
lengthListExample = Refl

sumList : List Nat -> Nat
sumList = foldList (+) 0

sumListExample : sumList [1, 2, 3] = 6
sumListExample = Refl



{-
Rose trees.
-}

{-
As an encore, we can also do rose trees, which are interesting because the
definition involves the composition with another indexed functor we've
previousle defined.
-}

data Rose : (a : Type) -> Type where
    Fork : a -> List (Rose a) -> Rose a

CodeRoseFunctor : IxFun (Either () ()) ()
CodeRoseFunctor = Product (Input (Left ())) (Composition IsoList (Input (Right ())))

{-
GPIF seems to favour using the equivalent of `CodeList' here for some reason,
but `IsoList' is a first class citizen in the universe, and using it directly
makes everything a little bit easier.
-}

CodeRose : IxFun () ()
CodeRose = Fix CodeRoseFunctor

fromRose : {r : IndexedType ()} -> {o : ()} -> Rose (r o) -> interp CodeRose r o
fromRose {r = r} {o = ()} (Fork x xs) =
        In (x, imap {r = Rose . r} {s = interp CodeRose r} IsoList f () xs)
    where
        %assert_total
        f : (Rose . r) `arrow` interp CodeRose r
        f () = fromRose

toRose : {r : IndexedType ()} -> {o : ()} -> interp CodeRose r o -> Rose (r o)
toRose {r = r} {o = ()} (In (x, xs)) =
        Fork x (imap {r = interp CodeRose r} {s = Rose . r} IsoList f () xs)
    where
        %assert_total
        f : interp CodeRose r `arrow` (Rose . r)
        f () = toRose

someRoseTree : Rose Nat
someRoseTree = Fork 1 [Fork 2 []]

anotherRoseTree : Rose Nat
anotherRoseTree = Fork 1 [Fork 2 [], Fork 3 [Fork 4 [], Fork 5 []]]

toFromRoseExample1 :
        toRose {r = const Nat} {o = ()} (fromRose {r = const Nat} {o = ()} someRoseTree) = someRoseTree
toFromRoseExample1 = Refl

toFromRoseExample2 :
        toRose {r = const Nat} {o = ()} (fromRose {r = const Nat} {o = ()} anotherRoseTree) = anotherRoseTree
toFromRoseExample2 = Refl

isoRose : (r : IndexedType ()) -> (o : ()) ->
        Isomorphic (Rose (r o)) (interp CodeRose r o)
isoRose r o =
        MkIso
            (fromRose {r = r} {o = o})
            (toRose {r = r} {o = o})
            (\_ => believe_me ())
            (\_ => believe_me ())

IsoRose : IxFun () ()
IsoRose = Iso CodeRose (\f, t => Rose (f t)) isoRose

{-
With isomorphism "established," we can get to concrete maps and folds once
again.
-}

mapRose : {a : Type} -> {b : Type} -> (a -> b) -> Rose a -> Rose b
mapRose {a = a} {b = b} f =
        imap {r = const a} {s = const b} IsoRose (lift f) ()

mapRoseExample : mapRose succ someRoseTree = Fork 2 [Fork 3 []]
mapRoseExample = Refl

foldRose : {a : Type} -> {r : Type} -> (a -> List r -> r) -> Rose a -> r
foldRose {a = a} {r = r} f xs =
        cata {r = const a} {s = const r}
                (baseFunctor (fromRose {r = const a} {o = ()} xs)) f' () (fromRose xs)
    where
        f' : interp CodeRoseFunctor (union (const a) (const r)) `arrow` const r
        f' () (x, y) = f x y

{-
For some reason, the implementation in GPIF is much more involved, as far as
I can tell -- unnecessarily so (even accounting for the use of `CodeList'
instead).
-}

sumRose : Rose Nat -> Nat
sumRose = foldRose (\x, xs => x + sumList xs)

sumRoseExample1 : sumRose someRoseTree = 3
sumRoseExample1 = Refl

sumRoseExample2 : sumRose anotherRoseTree = 15
sumRoseExample2 = Refl

