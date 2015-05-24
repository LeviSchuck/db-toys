module FactQueries where

import qualified Data.Map.Strict as M
import qualified Control.Monad.RWS.Strict as RWS
import Control.Monad
import Data.Maybe
import Data.List

import Debug.Trace

-- Let's try a strings approach.

type EntityID = String
type Attribute = String
type Value = String

data Kind = Single | Set
  deriving(Eq, Ord, Show)

data Fact = Fact EntityID Attribute Kind Value
  deriving(Eq, Ord, Show)

data Identifier
  = Blank
  | B String
  | L String
  deriving(Eq, Ord, Show)

data RetKind
  = Only Identifier
--  | First [Identifier]
  | Tuples [Identifier]
  deriving(Eq, Ord, Show)

data Q
  = Bind String String
  | Lookup Identifier Identifier Kind Identifier
  deriving(Eq, Ord, Show)


someFacts :: [Fact]
someFacts =
  [ Fact "1" "person" Single "Clay"
  , Fact "2" "person" Single "Josh"
  , Fact "3" "person" Single "Lyosha"
  , Fact "4" "person" Single "Carl"
  , Fact "5" "person" Single "Levi"
  , Fact "1" "hair" Single "Black"
  , Fact "2" "hair" Single "Bald"
  , Fact "3" "hair" Single "Sand"
  , Fact "4" "hair" Single "Black"
  , Fact "5" "hair" Single "Sand"
  , Fact "1" "friend" Set "3"
  , Fact "1" "friend" Set "4"
  , Fact "2" "friend" Set "3"
  , Fact "2" "friend" Set "5"
  , Fact "3" "friend" Set "1"
  , Fact "3" "friend" Set "2"
  , Fact "3" "friend" Set "4"
  , Fact "3" "friend" Set "5"
  , Fact "4" "friend" Set "1"
  , Fact "4" "friend" Set "3"
  , Fact "4" "friend" Set "5"
  , Fact "5" "friend" Set "2"
  , Fact "5" "friend" Set "3"
  , Fact "5" "friend" Set "4"
  , Fact "1" "hobby" Set "anime"
  , Fact "2" "hobby" Set "cooking"
  , Fact "2" "hobby" Set "movies"
  , Fact "3" "hobby" Set "electronics"
  , Fact "3" "hobby" Set "programming"
  , Fact "4" "hobby" Set "games"
  , Fact "5" "hobby" Set "movies"
  , Fact "5" "hobby" Set "anime"
  , Fact "5" "hobby" Set "electronics"
  , Fact "5" "hobby" Set "programming"
  , Fact "1" "app" Single "EC"
  , Fact "2" "app" Single "R"
  , Fact "3" "app" Single "R"
  , Fact "4" "app" Single "D"
  , Fact "5" "app" Single "B"

  ]

query1 :: [Q]
query1 =
  [ Lookup (B "me") (L "person") Single (L "Levi")
  , Lookup (B "me") (L "friend") Set (B "friend")
  , Lookup (B "me") (L "hobby") Set (B "hobby")
  , Lookup (B "friend") (L "person") Single (B "name")
  , Lookup (B "friend") (L "hair") Single (B "hair")
  , Lookup (B "friend") (L "hobby") Set (B "hobby")
  ]



type TState = M.Map String String
type TWrite = [[String]]
type TRead = [Fact]

ex :: [Q] -> [String] -> RWS.RWS TRead TWrite TState ()
ex [] rs = do
  s <- RWS.get
  vs <- forM rs $ \r -> do
    return $ case M.lookup r s of
      Just res -> res
      Nothing  -> ""
  RWS.tell [vs]
ex (q:qs) rs = case q of
  Bind k v -> do
    RWS.modify $ M.insert k v
    ex qs rs
  Lookup i a k v -> do
    db <- RWS.ask
    literalize i a k v db
  where
    f1 (Fact p _ _ _) = p
    f2 (Fact _ p _ _) = p
    f3 (Fact _ _ p _) = p
    f4 (Fact _ _ _ p) = p
    fdb1 (L i) db = filter (\f -> f1 f == i) db
    fdb1 _     db = db
    fdb2 (L a) db = filter (\f -> f2 f == a) db
    fdb2 _     db = db
    fdb3 k db     = filter (\f -> f3 f == k) db
    fdb4 (L v) db = filter (\f -> f4 f == v) db
    fdb4 _     db = db
    literalize i a k v db = do
      let db1 = fdb1 i db
          db2 = fdb2 a db1
          db3 = fdb3 k db2
          db4 = fdb4 v db3
      investigate i a k v db4
    pinvestigate i e db c = do
      s <- RWS.get
      case M.lookup i s of
        Nothing -> do
          let ts = nub $ map e db
          forM_ ts $ \t -> do
            RWS.modify $ M.insert i t
            c investigate (L t)
          RWS.put s
        Just v -> do
          c literalize (L v)
    investigate (B i) a k v db = pinvestigate i f1 db
      (\f t -> f t a k v db)
    investigate i (B a) k v db = pinvestigate a f2 db
      (\f t -> f i t k v db)
    investigate i a k (B v) db = pinvestigate v f4 db
      (\f t -> f i a k t db)
    investigate _ _ _ _ db = when (not $ null db) $ do
      ex qs rs

      
