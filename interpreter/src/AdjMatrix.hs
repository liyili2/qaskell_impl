module AdjMatrix
  where

newtype AdjMatrix a = AdjMatrix [[Maybe a]]
  deriving (Functor, Foldable)

completeGraph :: [a] -> AdjMatrix (a, a)
completeGraph nodes =
  AdjMatrix $
  map (\x -> map (\y -> Just (x, y)) nodes)
          nodes

updateNodeContents :: AdjMatrix a -> [b] -> AdjMatrix (b, b)
updateNodeContents (AdjMatrix adj) nodes =
  AdjMatrix $
  zipWith (\x row ->
              zipWith (\y entry ->
                          fmap (const (x, y)) entry)
                      nodes
                      row)
          nodes
          adj

-- chooseNodeContents :: Functor f =>
--   AdjMatrix (a, a) ->
--   f [Weighted w b] ->
--   f (AdjMatrix (Weighted w b, Weighted w b))
-- chooseNodeContents adj = fmap (updateNodeContents adj)

