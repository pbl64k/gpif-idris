
%default total

record Isomorphic a b where
    constructor MkIso
    from : a -> b
    to : b -> a
    iso1 : (x : a) -> to (from x) = x
    iso2 : (x : b) -> from (to x) = x

Indexed : Type -> Type
Indexed index = index -> Type

IndexedFunctor : Type -> Type -> Type
IndexedFunctor inputIndex outputIndex = Indexed inputIndex -> Indexed outputIndex

choice : Indexed firstIndex -> Indexed secondIndex ->
        Indexed (Either firstIndex secondIndex)
choice f g = either f g

mutual
    data IxFun : (i : Type) -> (o : Type) -> Type where
        Zero : IxFun i o
        One : IxFun i o
        Sum : IxFun i o -> IxFun i o -> IxFun i o
        Product : IxFun i o -> IxFun i o -> IxFun i o
        Composition : {m : Type} -> IxFun m o -> IxFun i m -> IxFun i o
        Iso : (c : IxFun i o) -> (d : IndexedFunctor i o) ->
                ((r : Indexed i) -> (out : o) -> Isomorphic (d r out) (interp c r out)) ->
                IxFun i o
        Fix : IxFun (Either i o) o -> IxFun i o
        Const : i -> IxFun i o
    
    data Mu : (f : IxFun (Either i o) o) -> (r : Indexed i) ->
            (out : o) -> Type where
        In : interp f (choice r (Mu f r)) o -> Mu f r o

    interp : IxFun i o -> IndexedFunctor i o
    interp Zero _ _ = Void
    interp One _ _ = ()
    interp (Sum f g) r o = Either (interp f r o) (interp g r o)
    interp (Product f g) r o = (interp f r o, interp g r o)
    interp (Composition f g) r o = (interp f . interp g) r o
    interp (Iso _ d _) r o = d r o
    interp (Fix f) r o = Mu f r o
    interp (Const i) r _ = r i

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

isoBool : (r : Indexed Void) -> (o : ()) ->
        Isomorphic Bool (interp BoolF r o)
isoBool r o =
        MkIso
            (fromBool {r = r} {o = o})
            (toBool {r = r} {o = o})
            isoBool1
            (isoBool2 {r = r} {o = o})

IsoBool : IxFun Void ()
IsoBool = Iso BoolF (\_, _ => Bool) isoBool

ListF : IxFun (Either () ()) ()
ListF = Sum One (Product (Const (Left ())) (Const (Right ())))

FList : IxFun () ()
FList = Fix ListF

fromList : {r : Indexed ()} -> {o : ()} -> List (r o) -> interp FList r o
fromList [] = In (Left ())
fromList {o = ()} (x :: xs) = In (Right (x, fromList xs))

%assert_total
toList : {r : Indexed ()} -> {o : ()} -> interp FList r o -> List (r o)
toList (In (Left ())) = []
toList {o = ()} (In (Right (x, xs))) = x :: toList xs
-- Curiously, just adding xs0@ triggers a type mismatch. Fascinating.
--toList {o = ()} xs0@(In (Right (x, xs))) = x :: toList xs

isoList : (r : Indexed ()) -> (o : ()) ->
        Isomorphic (List (r o)) (interp FList r o)
isoList r o =
        MkIso
            (fromList {r = r} {o = o})
            (toList {r = r} {o = o})
            (\_ => believe_me ())
            (\_ => believe_me ())

IsoList : IxFun () ()
IsoList = Iso FList (\f, t => List (f t)) isoList

arrow : {i : Type} -> Indexed i -> Indexed i -> Type
arrow {i = i} r s = (inp : i) -> r inp -> s inp

merge : arrow r u -> arrow s v -> arrow (choice r s) (choice u v)
merge f _ (Left x) = f x
merge _ f (Right x) = f x

fanout : (a -> b) -> (a -> c) -> a -> (b, c)
fanout f g x = (f x, g x)

imap : {i : Type} -> {o : Type} -> {r : Indexed i} -> {s : Indexed i} ->
        (c : IxFun i o) -> arrow r s -> arrow (interp c r) (interp c s)
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
        f' : arrow (choice r (Mu g r)) (choice s (Mu g s))
        f' = (merge f (imap (Fix g) f))
imap (Const i) f _ x = f i x

lift : {i : Type} -> (a -> b) -> arrow {i = i} (const a) (const b)
lift f _ x = f x

mapList : {a : Type} -> {b : Type} -> (a -> b) -> (List a -> List b)
mapList {a = a} {b = b} f =
        imap {r = const a} {s = const b} IsoList (lift f) ()

mapListExample : mapList succ [1, 2, 3] = [2, 3, 4]
mapListExample = Refl

idArrow : {i : Type} -> {r : Indexed i} -> arrow r r
idArrow _ = id

cata : {i : Type} -> {o : Type} -> {r : Indexed i} -> {s : Indexed o} ->
        (c : IxFun (Either i o) o) -> arrow (interp c (choice r s)) s ->
        arrow (interp (Fix c) r) s
cata {i = i} {o = o} {r = r} {s = s} c phi out (In x) =
        phi out (imap {r = r'} {s = s'} c f out x)
    where
        r' : Indexed (Either i o)
        r' = choice r (Mu c r)
        s' : Indexed (Either i o)
        s' = choice r s
        %assert_total
        f : arrow r' s'
        f = merge (idArrow {r = r}) (cata {r = r} {s = s} c phi)

partial
ana : {i : Type} -> {o : Type} -> {r : Indexed i} -> {s : Indexed o} ->
        (c : IxFun (Either i o) o) -> arrow s (interp c (choice r s)) ->
        arrow s (interp (Fix c) r)
ana {i = i} {o = o} {r = r} {s = s} c psy out x =
        In (imap {r = r'} {s = s'} c f out (psy out x))
    where
        r' : Indexed (Either i o)
        r' = choice r s
        s' : Indexed (Either i o)
        s' = choice r (Mu c r)
        partial
        f : arrow r' s'
        f = merge (idArrow {r = r}) (ana {r = r} {s = s} c psy)

partial
hylo : {i : Type} -> {o : Type} -> {r : Indexed i} -> {s : Indexed o} ->
        {t : Indexed o} -> (c : IxFun (Either i o) o) ->
        arrow (interp c (choice r t)) t -> arrow s (interp c (choice r s)) ->
        arrow s t
hylo {i = i} {o = o} {r = r} {s = s} {t = t} c phi psy out x =
        phi out (imap {r = r'} {s = s'} c f out (psy out x))
    where
        r' : Indexed (Either i o)
        r' = choice r s
        s' : Indexed (Either i o)
        s' = choice r t
        partial
        f : arrow r' s'
        f = merge (idArrow {r = r}) (hylo {r = r} {s = s} {t = t} c phi psy)

para : {i : Type} -> {o : Type} -> {r : Indexed i} -> {s : Indexed o} ->
        (c : IxFun (Either i o) o) ->
        arrow (interp c (choice r (\o => Pair (s o) (interp (Fix c) r o)))) s ->
        arrow (interp (Fix c) r) s
para {i = i} {o = o} {r = r} {s = s} c phi out (In x) =
        phi out (imap {r = r'} {s = s'} c f out x)
    where
        r' : Indexed (Either i o)
        r' = choice r (Mu c r)
        s' : Indexed (Either i o)
        s' = choice r (\o => Pair (s o) (interp (Fix c) r o))
        %assert_total
        f : arrow r' s'
        f = merge (idArrow {r = r}) (\ix => fanout (para {r = r} {s = s} c phi ix) id)

{-
Metamorphisms and apomorphisms are left as an exercise for the reader. Since
they're dual to hylomorphisms and paramorphisms, the derivation should be
"easy." (Cf. cata and ana.)
-}

foldr : {a : Type} -> {r : Type} -> (a -> r -> r) -> r -> List a -> r
foldr {a = a} {r = r} c n xs =
        cata {r = const a} {s = const r} ListF phi () (fromList xs)
    where
        phi : () -> Either () (a, r) -> r
        phi = \_ => (either (const n) (uncurry c))

foldrExample : Main.foldr (+) 0 [1, 2, 3] = 6
foldrExample = Refl

length : List a -> Nat
length = Main.foldr (const succ) 0

data Rose : (a : Type) -> Type where
    Fork : a -> List (Rose a) -> Rose a

RoseF : IxFun (Either () ()) ()
RoseF = Product (Const (Left ())) (Composition FList (Const (Right ())))

FRose : IxFun () ()
FRose = Fix RoseF

fromRose : {r : Indexed ()} -> {o : ()} -> Rose (r o) -> interp FRose r o
fromRose {r = r} {o = ()} (Fork x xs) =
        In (x, fromList (imap {r = Rose . r} {s = interp FRose r} IsoList f () xs))
    where
        %assert_total
        f : arrow (Rose . r) (interp FRose r)
        f () = fromRose

toRose : {r : Indexed ()} -> {o : ()} -> interp FRose r o -> Rose (r o)
toRose {r = r} {o = ()} (In (x, xs)) =
        Fork x (imap {r = interp FRose r} {s = Rose . r} IsoList f () (toList xs))
    where
        %assert_total
        f : arrow (interp FRose r) (Rose . r)
        f () = toRose

roseTree : Rose Nat
roseTree = (Fork 1 [Fork 2 []])

toFromRose : toRose {r = const Nat} {o = ()} (fromRose {r = const Nat} {o = ()} roseTree) = roseTree
toFromRose = Refl

isoRose : (r : Indexed ()) -> (o : ()) ->
        Isomorphic (Rose (r o)) (interp FRose r o)
isoRose r o =
        MkIso
            (fromRose {r = r} {o = o})
            (toRose {r = r} {o = o})
            (\_ => believe_me ())
            (\_ => believe_me ())

IsoRose : IxFun () ()
IsoRose = Iso FRose (\f, t => Rose (f t)) isoRose

