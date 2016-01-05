import Data.LinearProgram

import Graphics.Rendering.Chart.Easy
import Graphics.Rendering.Chart.Backend.Cairo
import System.Directory

import Control.Arrow
import Control.Monad
import Data.List


main :: IO ()
main = do
   graphCosts <- forM [10,100,1000,5000] $ \n -> do
      cs <- forM [2**lv | lv<-[0,0.2 .. 13]] $ \v -> do
         let g = starGraph n v
         (Success, Just (c,_)) <- glpSolveVars mipDefaults (vertexCover_LP g)
         return (v,c)
      return (n,cs)
   toPdfFile (520,480) "starcosts" $ do
      layout_x_axis . laxis_title .= "V" 
      layout_y_axis . laxis_title .= "cost" 
      forM_ graphCosts $ \(n,cs) -> do
         plot $ line ("N = "++show n) [(logDom***logDom)<$>cs]
         


-- Definition of the graph type
-- -- --

type VertexID = Int

-- | Graph with annotated nodes (no annotated/weighted edges)
data Graph a = Graph { graphVerts :: [a], graphEdges :: [(VertexID, VertexID)] }

type Cost = Double


-- Linear programming
-- -- --

-- | Create, for a graph with vertex-costs, a linear program corresponding to
--   the vertex-cover relaxation.
vertexCover_LP :: Graph Cost -> LP VertexID Cost
vertexCover_LP (Graph vCosts edges) = execLPM $ do

    forM_ [0 .. length vCosts-1] $ \v -> do
       setVarKind v ContVar
       varGeq v 0; varLeq v 1  -- for every vertex a variable in interval [0,1]
    
    setDirection Min
    setObjective $ linCombination    -- minimise linear combination of cost
                      (zip vCosts [0..])
    
    forM_ edges $                                 -- require each edge to be
             \(u,w) -> (1*&u ^+^ 1*&w) `geqTo` 1  -- "on average" contained



-- | Create a star-shaped graph in which the central vertex has a given cost
--   (the satellites have unit cost).
starGraph :: Int -> Cost -> Graph Cost
starGraph n v = Graph { graphVerts = v : replicate n 1
                      , graphEdges = [ (k,0) | k <- [1..n] ] }



-- Plotting utility
-- -- --

toPdfFile :: (ToRenderable r, Default r) => (Int,Int) -> FilePath -> EC r () -> IO ()
toPdfFile sz fn plot = do
         toFile ((fo_format .~ PDF) . (fo_size .~ sz) $ def) fn' plot
 where fn' | ".pdf"`isSuffixOf`fn  = fn
           | otherwise             = fn++".pdf"

logDom :: RealFrac a => a -> LogValue
logDom = realToFrac

