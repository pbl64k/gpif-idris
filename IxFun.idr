
%default total

record Isomorphic a b where
    constructor MkIso
    from : a -> b
    to : b -> a
    iso1 : (x : a) -> to (from x) = x
    iso2 : (x : b) -> from (to x) = x

Indexed : Type -> Type
Indexed i = i -> Type

IndexedFunctor : Type -> Type -> Type
IndexedFunctor i o = Indexed i -> Indexed o

choice : Indexed i -> Indexed j -> Indexed (Either i j)
choice r s (Left i) = r i
choice r s (Right j) = s j

mutual
    data IxFun : (i : Type) -> (o : Type) -> Type where
        Zero : IxFun i o
        One : IxFun i o
        Sum : IxFun i o -> IxFun i o -> IxFun i o
        Product : IxFun i o -> IxFun i o -> IxFun i o
        Composition : IxFun m o -> IxFun i m -> IxFun i o
        Iso : (c : IxFun i o) -> (d : IndexedFunctor i o) ->
                ((r : Indexed i) -> (out : o) -> Isomorphic (d r out) (interp c r out)) -> IxFun i o
        Fix : IxFun (Either i o) o -> IxFun i o
        Const : i -> IxFun i o
    
    data Mu : (f : IxFun (Either i o) o) -> (r : Indexed i) -> (out : o) -> Type where
        In : interp f (choice r (Mu f r)) o -> Mu f r o

    interp : IxFun i o -> IndexedFunctor i o
    interp Zero r o = Void
    interp One r o = ()
    interp (Sum f g) r o = Either (interp f r o) (interp g r o)
    interp (Product f g) r o = (interp f r o, interp g r o)
    interp (Composition f g) r o = (interp f . interp g) r o
    interp (Iso c d e) r o = d r o
    interp (Fix f) r o = Mu f r o
    interp (Const i) r o = r i

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

isoBool : (r : Indexed Void) -> (o : ()) -> Isomorphic Bool (interp BoolF r o)
isoBool r o =
        MkIso
            (fromBool {r = r} {o = o})
            (toBool {r = r} {o = o})
            isoBool1
            (isoBool2 {r = r} {o = o})

MyBool : IxFun Void ()
MyBool = Iso BoolF (\_, _ => Bool) isoBool

ListF : IxFun (Either () ()) ()
ListF = Sum One (Product (Const (Left ())) (Const (Right ())))

FList : IxFun () ()
FList = Fix ListF

fromList : List (r o) -> interp FList r o
fromList [] = In (Left ())
fromList {o = ()} (x :: xs) = In (Right (x, fromList xs))

partial
toList : interp FList r o -> List (r o)
toList (In (Left ())) = []
toList {o = ()} (In (Right (x, xs))) = x :: toList xs

partial
isoList : (r : Indexed ()) -> (o : ()) -> Isomorphic (List (r o)) (interp FList r o)
isoList r o =
        MkIso
            (fromList {r = r} {o = o})
            (toList {r = r} {o = o})
            (\_ => believe_me ())
            (\_ => believe_me ())

partial
MyList : IxFun () ()
MyList = Iso (Fix ListF) (\f, t => List (f t)) isoList

arrow : Indexed i -> Indexed i -> Type
arrow r s = (inp : _) -> r inp -> s inp

merge : arrow r u -> arrow s v -> arrow (choice r s) (choice u v)
merge f _ (Left x) = f x
merge _ f (Right x) = f x

imap : {i : Type} -> {o : Type} -> {r : Indexed i} -> {s : Indexed i} -> (c : IxFun i o) -> arrow r s -> arrow (interp c r) (interp c s)
imap One f o () = ()
imap (Sum g h) f o (Left x) = Left (imap g f o x)
imap (Sum g h) f o (Right x) = Right (imap h f o x)
imap (Product g h) f o (x, y) = (imap g f o x, imap h f o y)
--imap (Composition g h) f o x = imap g (imap h f) o x
--imap (Fix g) f o (In x) = In (imap g (merge f (imap (Fix g) f)) o x)
imap (Const i) f o x = f i x

