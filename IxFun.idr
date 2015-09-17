
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
a single inhabitant -- similarly to how functions of type `() -> a' are
isomorphic to values of type `a'.

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
illustrate the stuff I've introduced so far:
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

choice : IndexedType firstIndex -> IndexedType secondIndex ->
        IndexedType (Either firstIndex secondIndex)
choice f g = either f g

{-
For convenience, `choice' produces a "sum" of indexed types, that is:
-}

anotherIndexedType : IndexedType (Either () Bool)
anotherIndexedType = choice (const Bool) someIndexedType

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
arrow {index = index} ixTypeFrom ixTypeTo =
        (inp : index) -> ixTypeFrom inp -> ixTypeTo inp

{-
`arrow' produces the type or morphisms (generalized functions) between two
indexed types using the same index.

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

split : r `arrow` u -> s `arrow` v -> choice r s `arrow` choice u v
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

idArrow : {i : Type} -> {r : IndexedType i} -> r `arrow` r
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
types, maps and folds?..
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
First, we build an encoding.
-}

    data Mu : (baseFunctorRepr : IxFun (Either inputIndex outputIndex) outputIndex) ->
            (inputType : IndexedType inputIndex) -> (out : outputIndex) -> Type where
        In : interp baseFunctorRepr (choice inputType (Mu baseFunctorRepr inputType)) outputIndex ->
                Mu baseFunctorRepr inputType outputIndex

    interp : IxFun i o -> IndexedFunctor i o
    interp Zero _ _ = Void
    interp One _ _ = ()
    interp (Sum f g) r o = Either (interp f r o) (interp g r o)
    interp (Product f g) r o = (interp f r o, interp g r o)
    interp (Composition f g) r o = (interp f . interp g) r o
    interp (Iso _ d _) r o = d r o
    interp (Fix f) r o = Mu f r o
    interp (Input i) r _ = r i

baseFunctor : {f : IxFun (Either i o) o} -> Mu f _ _ -> IxFun (Either i o) o
baseFunctor {f = f} _ = f

imap : {i : Type} -> {o : Type} -> {r : IndexedType i} -> {s : IndexedType i} ->
        (c : IxFun i o) -> r `arrow` s -> interp c r `arrow` interp c s
imap One f _ () = ()
imap (Sum g _) f o (Left x) = Left (imap g f o x)
imap (Sum _ h) f o (Right x) = Right (imap h f o x)
imap (Product g h) f o (x, y) = (imap g f o x, imap h f o y)
imap {r = r} {s = s} (Composition g h) f o x =
        imap {r = interp h r} {s = interp h s} g (imap h f) o x
imap {r = r} {s = s} (Iso c d e) f o x = to ep2 (imap c f o (from ep1 x))
    where
        ep1 : Isomorphic (d r o) (interp c r o)
        ep1 = e r o
        ep2 : Isomorphic (d s o) (interp c s o)
        ep2 = e s o
imap {r = r} {s = s} (Fix g) f o (In x) =
        In (imap {r = choice r (Mu g r)} {s = choice s (Mu g s)} g f' o x)
    where
        %assert_total
        f' : choice r (Mu g r) `arrow` choice s (Mu g s)
        f' = (split f (imap (Fix g) f))
imap (Input i) f _ x = f i x

{-
Catamorphisms are folds.
-}

cata : {i : Type} -> {o : Type} -> {r : IndexedType i} -> {s : IndexedType o} ->
        (c : IxFun (Either i o) o) -> interp c (choice r s) `arrow` s ->
        interp (Fix c) r `arrow` s
cata {i = i} {o = o} {r = r} {s = s} c phi out (In x) =
        phi out (imap {r = r'} {s = s'} c f out x)
    where
        r' : IndexedType (Either i o)
        r' = choice r (Mu c r)
        s' : IndexedType (Either i o)
        s' = choice r s
        %assert_total
        f : r' `arrow` s'
        f = split (idArrow {r = r}) (cata {r = r} {s = s} c phi)

{-
Anamorphisms are unfolds.

Note that we can't really guarantee termination here. Unfortunately, codata
is outside of the universe, so there doesn't seem to be a lot to do here in
a principled fashion.
-}

partial
ana : {i : Type} -> {o : Type} -> {r : IndexedType i} -> {s : IndexedType o} ->
        (c : IxFun (Either i o) o) -> s `arrow` interp c (choice r s) ->
        s `arrow` interp (Fix c) r
ana {i = i} {o = o} {r = r} {s = s} c psy out x =
        In (imap {r = r'} {s = s'} c f out (psy out x))
    where
        r' : IndexedType (Either i o)
        r' = choice r s
        s' : IndexedType (Either i o)
        s' = choice r (Mu c r)
        partial
        f : r' `arrow` s'
        f = split (idArrow {r = r}) (ana {r = r} {s = s} c psy)

{-
Hylomorphisms are equivalent to a composition of an unfold with a fold. Since
unfolds are involved, this is also partial.
-}

partial
hylo : {i : Type} -> {o : Type} -> {r : IndexedType i} -> {s : IndexedType o} ->
        {t : IndexedType o} -> (c : IxFun (Either i o) o) ->
        interp c (choice r t) `arrow` t -> s `arrow` interp c (choice r s) ->
        s `arrow` t
hylo {i = i} {o = o} {r = r} {s = s} {t = t} c phi psy out x =
        phi out (imap {r = r'} {s = s'} c f out (psy out x))
    where
        r' : IndexedType (Either i o)
        r' = choice r s
        s' : IndexedType (Either i o)
        s' = choice r t
        partial
        f : r' `arrow` s'
        f = split (idArrow {r = r}) (hylo {r = r} {s = s} {t = t} c phi psy)

{-
Paramorphisms are generalized folds, commonly described as "using their value
and keeping it too."
-}

para : {i : Type} -> {o : Type} -> {r : IndexedType i} -> {s : IndexedType o} ->
        (c : IxFun (Either i o) o) ->
        interp c (choice r (\o => Pair (s o) (interp (Fix c) r o))) `arrow` s ->
        interp (Fix c) r `arrow` s
para {i = i} {o = o} {r = r} {s = s} c phi out (In x) =
        phi out (imap {r = r'} {s = s'} c f out x)
    where
        r' : IndexedType (Either i o)
        r' = choice r (Mu c r)
        s' : IndexedType (Either i o)
        s' = choice r (\o => Pair (s o) (interp (Fix c) r o))
        %assert_total
        f : r' `arrow` s'
        f = split (idArrow {r = r}) (\ix => fanout (para {r = r} {s = s} c phi ix) id)

{-
Metamorphisms and apomorphisms are left as an exercise for the reader. Since
they're dual to hylomorphisms and paramorphisms correspondingly, the
derivation should be "easy." (Cf. `cata' and `ana'.)
-}

{-
Booleans.
-}

BoolF : IxFun Void ()
BoolF = Sum One One

fromBool : Bool -> interp BoolF r o
fromBool False = Left ()
fromBool True = Right ()

toBool : interp BoolF r o -> Bool
toBool (Left ()) = False
toBool (Right ()) = True

isoBool1 : (b : Bool) -> toBool (fromBool b) = b
isoBool1 False = Refl
isoBool1 True = Refl

isoBool2 : (b : interp BoolF r o) -> fromBool (toBool b) = b
isoBool2 (Left ()) = Refl
isoBool2 (Right ()) = Refl

isoBool : (r : IndexedType Void) -> (o : ()) ->
        Isomorphic Bool (interp BoolF r o)
isoBool r o =
        MkIso
            (fromBool {r = r} {o = o})
            (toBool {r = r} {o = o})
            isoBool1
            (isoBool2 {r = r} {o = o})

IsoBool : IxFun Void ()
IsoBool = Iso BoolF (\_, _ => Bool) isoBool

{-
Cons-cell lists.
-}

ListF : IxFun (Either () ()) ()
ListF = Sum One (Product (Input (Left ())) (Input (Right ())))

FList : IxFun () ()
FList = Fix ListF

fromList : {r : IndexedType ()} -> {o : ()} -> List (r o) -> interp FList r o
fromList [] = In (Left ())
fromList {o = ()} (x :: xs) = In (Right (x, fromList xs))

%assert_total
toList : {r : IndexedType ()} -> {o : ()} -> interp FList r o -> List (r o)
toList (In (Left ())) = []
toList {o = ()} (In (Right (x, xs))) = x :: toList xs
-- Curiously, just adding xs0@ triggers a type mismatch. Fascinating.
--toList {o = ()} xs0@(In (Right (x, xs))) = x :: toList xs

isoList : (r : IndexedType ()) -> (o : ()) ->
        Isomorphic (List (r o)) (interp FList r o)
isoList r o =
        MkIso
            (fromList {r = r} {o = o})
            (toList {r = r} {o = o})
            (\_ => believe_me ())
            (\_ => believe_me ())

IsoList : IxFun () ()
IsoList = Iso FList (\f, t => List (f t)) isoList

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

foldListExample : foldList (+) 0 [1, 2, 3] = 6
foldListExample = Refl

lengthList : List a -> Nat
lengthList = foldList (const succ) 0

sumList : List Nat -> Nat
sumList = foldList (+) 0

{-
Rose trees.
-}

data Rose : (a : Type) -> Type where
    Fork : a -> List (Rose a) -> Rose a

RoseF : IxFun (Either () ()) ()
RoseF = Product (Input (Left ())) (Composition FList (Input (Right ())))

FRose : IxFun () ()
FRose = Fix RoseF

fromRose : {r : IndexedType ()} -> {o : ()} -> Rose (r o) -> interp FRose r o
fromRose {r = r} {o = ()} (Fork x xs) =
        In (x, fromList (imap {r = Rose . r} {s = interp FRose r} IsoList f () xs))
    where
        %assert_total
        f : (Rose . r) `arrow` interp FRose r
        f () = fromRose

toRose : {r : IndexedType ()} -> {o : ()} -> interp FRose r o -> Rose (r o)
toRose {r = r} {o = ()} (In (x, xs)) =
        Fork x (imap {r = interp FRose r} {s = Rose . r} IsoList f () (toList xs))
    where
        %assert_total
        f : interp FRose r `arrow` (Rose . r)
        f () = toRose

roseTree : Rose Nat
roseTree = (Fork 1 [Fork 2 []])

toFromRoseExample : toRose {r = const Nat} {o = ()} (fromRose {r = const Nat} {o = ()} roseTree) = roseTree
toFromRoseExample = Refl

isoRose : (r : IndexedType ()) -> (o : ()) ->
        Isomorphic (Rose (r o)) (interp FRose r o)
isoRose r o =
        MkIso
            (fromRose {r = r} {o = o})
            (toRose {r = r} {o = o})
            (\_ => believe_me ())
            (\_ => believe_me ())

IsoRose : IxFun () ()
IsoRose = Iso FRose (\f, t => Rose (f t)) isoRose

mapRose : {a : Type} -> {b : Type} -> (a -> b) -> Rose a -> Rose b
mapRose {a = a} {b = b} f = imap {r = const a} {s = const b} IsoRose (lift f) ()

mapRoseExample : mapRose succ roseTree = Fork 2 [Fork 3 []]
mapRoseExample = Refl

foldRose : {a : Type} -> {r : Type} -> (a -> List r -> r) -> Rose a -> r
foldRose {a = a} {r = r} f xs = cata {r = const a} {s = const r}
        (baseFunctor (fromRose {r = const a} {o = ()} xs)) f' () (fromRose xs)
    where
        f' : interp RoseF (choice (const a) (const r)) `arrow` const r
        f' () (x, y) = f x (toList y)

sumRose : Rose Nat -> Nat
sumRose = foldRose (\x, xs => x + sumList xs)

sumRoseExample : sumRose roseTree = 3
sumRoseExample = Refl

