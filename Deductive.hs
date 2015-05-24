module Deductive where

import Data.List
import Control.Monad
import Data.Maybe

import Debug.Trace

type Name = String
type Values = [String]
type KeyStr = String
data Identifier
  = Val String
  | Key KeyStr
  | Blank
  deriving(Eq, Ord, Show)

type Keys = [KeyStr]

type Params = [Identifier]

data Fact = Fact Name Values
  deriving(Eq, Ord, Show)


someData :: [Fact]
someData =
  [ Fact "person" ["jackson", "buyer"]
  , Fact "person" ["jeramy", "buyer"]
  , Fact "person" ["james", "buyer"]
  , Fact "person" ["john", "buyer"]
  , Fact "person" ["jerry", "buyer"]
  , Fact "person" ["jim", "buyer"]
  , Fact "person" ["jake", "buyer"]
  , Fact "person" ["ben", "seller"]
  , Fact "person" ["blake", "seller"]
  , Fact "person" ["brad", "seller"]
  , Fact "person" ["bruce", "seller"]
  , Fact "person" ["bill", "seller"]
  , Fact "person" ["bert", "seller"]
  , Fact "person" ["bob", "seller"]
  , Fact "person" ["barney", "seller"]
  , Fact "bought_from" ["jackson", "ben"]
  , Fact "bought_from" ["jackson", "blake"]
  , Fact "bought_from" ["jackson", "bruce"]
  , Fact "bought_from" ["jackson", "brad"]
  , Fact "bought_from" ["jackson", "bill"]
  , Fact "bought_from" ["jackson", "bob"]
  , Fact "bought_from" ["jake", "ben"]
  , Fact "bought_from" ["jake", "bert"]
  , Fact "bought_from" ["jeramy", "brad"]
  , Fact "bought_from" ["james", "ben"]
  , Fact "bought_from" ["jim", "ben"]
  , Fact "bought_from" ["jim", "bob"]
  , Fact "bought_from" ["john", "bruce"]
  , Fact "bought_from" ["john", "barney"]
  , Fact "bought_with" ["jackson", "jake"]
  , Fact "bought_with" ["jackson", "jeramy"]
  , Fact "bought_with" ["jackson", "jim"]
  , Fact "bought_with" ["jackson", "jerry"]
  ]


data Predicate = Pred Name Params
  deriving(Eq, Ord, Show)
data Rule = Rule Name [KeyStr] [Predicate]
  deriving(Eq, Ord, Show)

someRules :: [Rule]
someRules =
  [ Rule "bought_with" ["P1", "P2"]
    [ Pred "bought_with"
      [ Key "P2"
      , Key "P1"
      ]
    ]
  , Rule "bought_together" ["A", "P1", "P2"]
    [ Pred "bought_from"
      [ Key "P1"
      , Key "A"
      ]
    , Pred "bought_from"
      [ Key "P2"
      , Key "A"
      ]
    , Pred "bought_with"
      [ Key "P1"
      , Key "P2"
      ]
    ]
  ]


addFact :: [Fact] -> Fact -> [Fact]
addFact fs f = if elem f fs
  then fs
  else f:fs

apply :: [Rule] -> [Fact] -> [Fact]
apply rs fs = do
  r <- rs
  -- Rule Name KeyStr [Predicate]
  let Rule name keys preds = r
  let partial = do
      Pred pn params <- preds
      let ffs = filter (\(Fact n _) -> n == pn) fs
      f <- ffs
      let Fact _ vs = f
      let pvs = zip vs params
      guard $ all paramvals pvs
      return (f, pvs)
  -- THIS IS SO NOT EFFICIENT! DO NOT DO FOR REAL STUFF
  -- sequence creates a big huge list of combinations
  let kvs = sequence . grp . sort . nub $ do
      (_, ks) <- partial
      (v, k) <- ks
      case k of
        Key k' -> return (k', v)
        _ -> mzero
  ks <- kvs
  let asserts = do
      p <- preds
      let Pred pn params = p
      let params' = map (match ks) params
      return $ assertPred (Pred pn params')
  guard $ and asserts
  let lookups = catMaybes [lookup key ks | key <- keys]
  guard $ length lookups == length keys
  return $ Fact name lookups
  where
    paramvals (v1, Val v2) = v1 == v2
    paramvals _ = True
    grp = groupBy (\a b -> fst a == fst b)
    match ks (Key k) = let Just x = lookup k ks in Val x
    match _ k = k
    assertPred (Pred nm pred) = not . null $ do
      Fact n vs <- fs
      guard $ n == nm
      guard $ all paramvals $ zip vs pred
      return ()



expand :: [Fact] -> [Rule] -> [Fact]
expand fs rs = if l1 /= l2
  then expand expanded rs
  else fs
  where
    l1 = length fs
    derived = apply rs fs
    expanded = foldl addFact fs derived
    l2 = length expanded


{-
λ: let res = expand someData someRules 
λ: res \\ someData
[Fact "bought_together" ["brad","jeramy","jackson"]
,Fact "bought_together" ["bob","jim","jackson"]
,Fact "bought_together" ["ben","jim","jackson"]
,Fact "bought_together" ["ben","jake","jackson"]
,Fact "bought_together" ["brad","jackson","jeramy"]
,Fact "bought_together" ["bob","jackson","jim"]
,Fact "bought_together" ["ben","jackson","jim"]
,Fact "bought_together" ["ben","jackson","jake"]
,Fact "bought_with" ["jim","jackson"]
,Fact "bought_with" ["jerry","jackson"]
,Fact "bought_with" ["jeramy","jackson"]
,Fact "bought_with" ["jake","jackson"]]
-}
