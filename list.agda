module list where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)

  open import utils
  open import definitions

  data List : Set → Set where
    [] : {A : Set} → List A
    _::_ : {A : Set} → A → List A → List A

  _++_ : {A : Set} → List A → List A → List A
  [] ++ ys = ys
  (x :: xs) ++ ys = x :: (xs ++ ys)

  catUnitLeft : {A : Set} →
                (x : List A) →
                [] ++ x ≡ x
  catUnitLeft x = refl
  
  catUnitRight : {A : Set} →
                 (x : List A) →
                 x ++ [] ≡ x
  catUnitRight [] = refl
  catUnitRight (x₁ :: x) = cong (x₁ ::_) (catUnitRight x)

  catAssoc : {A : Set} →
             (x : List A) → (y : List A) → (z : List A) →
             (x ++ y) ++ z ≡ x ++ (y ++ z)
  catAssoc [] y z = refl
  catAssoc (x₁ :: x) y z = cong (x₁ ::_) (catAssoc x y z)
          

  mapList : {A B : Set} → (A → B) → List A → List B
  mapList f [] = []
  mapList f (x :: xs) = f x :: mapList f xs

  mapReplaceList : {A B : Set} → (f : A → B) → (g : A → B) →
                   ((x : A) → f x ≡ g x) →
                   (y : List A) →
                   mapList f y ≡ mapList g y
  mapReplaceList f g p [] = refl
  mapReplaceList f g p (x :: xs) =
    let p1 = cong (_:: mapList f xs) (p x)
        p2 = cong (g x ::_) (mapReplaceList f g p xs)
    in trans p1 p2

  ax1List : {A : Set} → (x : List A) →
            mapList id x ≡ x
  ax1List [] = refl
  ax1List (x :: xs) =
    let p2 = cong (_:: mapList id xs) refl
        p3 = cong (x ::_) (ax1List xs)
    in trans p2 p3

  ax2List : {A B C : Set} → (f : B → C) → (g : A → B) → (x : List A) →
            mapList (f ∘ g) x ≡ mapList f (mapList g x)
  ax2List f g [] = refl
  ax2List f g (x :: xs) =
    let p1 = cong (_:: mapList (f ∘ g) xs) refl
        p2 = cong (f (g x) ::_) (ax2List f g xs)
    in trans p1 p2

  𝐿ist : Functor List
  𝐿ist = functor mapList mapReplaceList ax1List ax2List

  unitListMorp : {A : Set} → Id A → List A
  unitListMorp x = x :: []

  unitListAxNat : {A B : Set} → (f : A → B) → (x : Id A) →
                  mapList f (unitListMorp x) ≡ unitListMorp (mapF 𝟙 f x)
  unitListAxNat f x = refl

  unitList : 𝟙 ~> 𝐿ist
  unitList = NT unitListMorp unitListAxNat

  --Util
  catListMor : {A B : Set} → (f : A → B) → (xs : List A) → (ys : List A) →
               mapList f (xs ++ ys) ≡ (mapList f xs) ++ (mapList f ys)
  catListMor f [] ys = refl
  catListMor f (x :: xs) ys = cong (f x ::_) (catListMor f xs ys)

  multListMorp : {A : Set} → (List <> List) A → List A
  multListMorp [] = []
  multListMorp (xs :: xss) = xs ++ multListMorp xss

  multListAxNat : {A B : Set} → (f : A → B) → (x : (List <> List) A) →
                  mapList f (multListMorp x) ≡ multListMorp (mapF (𝐿ist ∙ 𝐿ist) f x)
  multListAxNat f [] = refl
  multListAxNat f (xs :: xss) =
    let p1 = catListMor f xs (multListMorp xss)
        p2 = cong (mapList f xs ++_) (multListAxNat f xss)
    in trans p1 p2

  multList : (𝐿ist ∙ 𝐿ist) ~> 𝐿ist
  multList = NT multListMorp multListAxNat

  axUnitLeftList : {A : Set} → (x : (Id <> List) A) →
                   mor (multList ⊙ (unitList ◁ 𝐿ist)) x ≡ mor {𝔾 = 𝐿ist} 𝕦Left x
  axUnitLeftList [] = refl
  axUnitLeftList (x :: xs) = cong (x ::_) (axUnitLeftList xs)

  axUnitRightList : {A : Set} → (x : (List <> Id) A) →
                    mor (multList ⊙ (𝐿ist ▷ unitList)) x ≡ mor {𝔾 = 𝐿ist} 𝕦Right x
  axUnitRightList [] = refl
  axUnitRightList (x :: xs) = cong (x ::_) (axUnitRightList xs)

  axAssocList : {A : Set} → (x : ((List <> List) <> List) A) →
                mor (multList ⊙ (multList ◁ 𝐿ist)) x ≡ mor (multList ⊙ (𝐿ist ▷ multList)) x
  axAssocList [] = refl
  axAssocList (xss :: xsss) =
    let p1 : multListMorp (xss ++ multListMorp xsss) ≡ (multListMorp xss ++ multListMorp (multListMorp xsss))
        p1 = helper xss (multListMorp xsss)
        p2 = cong (multListMorp xss ++_) (axAssocList xsss)
    in trans p1 p2
    where helper : {A : Set} → (x : List (List A)) → (y : List (List A)) →
                   multListMorp (x ++ y) ≡ (multListMorp x ++ multListMorp y)
          helper [] y = refl
          helper (x₁ :: x) y =
            let p1 = cong (x₁ ++_) (helper x y)
                p2 = sym (catAssoc x₁ (multListMorp x) (multListMorp y))
            in trans p1 p2

  𝕃ist : Monad List
  𝕃ist = monad 𝐿ist unitList multList axUnitLeftList axUnitRightList axAssocList
