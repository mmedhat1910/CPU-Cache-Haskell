import Data.Foldable (Foldable)

data Item a = It Tag (Data a) Bool Int | NotPresent deriving (Show, Eq)

data Tag = T Int deriving (Show, Eq)

data Data a = D a deriving (Show, Eq)

convertBinToDec :: Integral a => a -> a
convertBinToDec bin = convertBinToDecH bin 0

convertBinToDecH 0 c = 0
convertBinToDecH bin c = (mod bin 10) * (2 ^ c) + convertBinToDecH (div bin 10) (c + 1)

replaceIthItem :: t -> [t] -> Int -> [t]
replaceIthItem item [] i = []
replaceIthItem item (x : xs) 0 = (item : xs)
replaceIthItem item (x : xs) i = (x : replaceIthItem item xs (i -1))

splitEvery :: Int -> [a] -> [[a]]
splitEvery n l = splitEveryH n l n []

splitEveryH n [] c acc = acc
splitEveryH n (x : xs) c [] = splitEveryH n xs (c -1) [[x]]
splitEveryH n (x : xs) c (y : ys)
  | c == 0 = (y : (splitEveryH n (x : xs) n ys))
  | otherwise = (splitEveryH n xs (c -1) ((y ++ [x]) : ys))

logBase2 :: Floating a => a -> a
logBase2 x = logBase 2 x

getNumBits :: (Integral a, RealFloat a1) => a1 -> [Char] -> [c] -> a
getNumBits numOfSets "fullyAssoc" _ = 0
getNumBits numOfSets "setAssoc" _ = ceiling (logBase2 numOfSets)
getNumBits lengthOfCache "directMap" _ = ceiling (logBase2 lengthOfCache)

fillZeros :: [Char] -> Int -> [Char]
fillZeros (x : xs) 0 = (x : xs)
fillZeros (x : xs) n = fillZeros ('0' : x : xs) (n -1)

getDataFromCache :: (Integral b, Eq a) => [Char] -> [Item a] -> [Char] -> b -> Output a

data Output a = Out (a, Int) | NoOutput deriving (Show, Eq)

getDataFromCache stringAddress cache "fullyAssoc" bitsNum = getDataFromCacheHelper (read stringAddress :: Int) 0 cache
getDataFromCache stringAddress cache "setAssoc" bitsNum =
  getDataFromCacheHelper (getTag1 (read stringAddress :: Int) bitsNum) 0 (getSet (splitEvery (div (length cache) (2 ^ bitsNum)) cache) (getDecIndex (read stringAddress :: Int) bitsNum))
getDataFromCache stringAddress cache "directMap" bitsNum =
  if (((getTagFromAddress bitsNum stringAddress) == (getTagFromItem item)) && ((getValidity item) == True))
    then Out (getDataFromItem item, 0)
    else NoOutput
  where
    item = getItemFromCache cache (getIndexDec stringAddress bitsNum)

getTagFromItem (It (T t) _ _ _) = t

getValidity (It _ _ validity _) = validity

getItemFromCache cache num = cache !! num

getIndexDec stringAddress bitsNum = convertBinToDec (mod ((read stringAddress) :: Int) (10 ^ bitsNum))

--getTagFromAddress :: (Eq t,Integral t) => t -> [Char] -> Int
getTagFromAddress bitsNum stringAddress = div (read stringAddress :: Int) (10 ^ bitsNum)

getDataFromItem (It _ (D d) _ _) = d

outputing (It _ (D d) _ _) = Out (d, 0)

getTag1 binAddress bitsNum = div binAddress (10 ^ bitsNum)

getIndex1 binAddress bitsNum = mod binAddress (10 ^ bitsNum)

getDecIndex binAddress bitsNum = convertBinToDec (getIndex1 binAddress bitsNum)

getSet (x : xs) 0 = x
getSet (x : xs) decIndex = getSet xs (decIndex -1)

getDataFromCacheHelper tag hops [] = NoOutput
getDataFromCacheHelper tag hops (It (T tag1) (D data1) b o : xs)
  | tag == tag1 && b == True = Out (data1, hops)
  | otherwise = getDataFromCacheHelper tag (hops + 1) xs

convertAddress :: (Integral b1, Integral b2) => b1 -> b2 -> p -> (b1, b1)
convertAddress binAddress bitsNum _ = (div binAddress (10 ^ bitsNum), mod binAddress (10 ^ bitsNum))

appendSplitted l = foldr (++) [] l

-- firstNth0 list item = idx
firstNth0 :: (Num p, Eq t) => [t] -> t -> p
firstNth0 [] _ = -1
firstNth0 (x : xs) item = if item == x then 0 else 1 + firstNth0 xs item

incrementOrder [] = []
incrementOrder ((It (T t) (D d) validBit order) : t1)
  | validBit = It (T t) (D d) validBit (order + 1) : incrementOrder t1
  | otherwise = It (T t) (D d) validBit order : incrementOrder t1

getMaxOrder :: [Item a] -> Int
getMaxOrder [] = -1
getMaxOrder ((It (T t) (D d) validBit order) : t1) = max order n where n = getMaxOrder t1

getMaxIndex :: [Item a] -> Int
getMaxIndex [] = -1
getMaxIndex ((It (T t) (D d) validBit order) : t1) = if order == maxOrder then 0 else 1 + getMaxIndex t1
  where
    maxOrder = getMaxOrder ((It (T t) (D d) validBit order) : t1)

getFirstInvIdx :: [Item a] -> Int
getFirstInvIdx [] = 0
getFirstInvIdx ((It (T t) (D d) validBit order) : t1) = if validBit == False then 0 else 1 + getFirstInvIdx t1

getFullTag :: Int -> [Char] -> Int -> [Char]
getFullTag t cacheType bitsnum
  | cacheType == "fullyAssoc" = fillZeros tag (6 - length tag)
  | otherwise = fillZeros tag (6 - bitsnum - length tag)
  where
    tag = show t -- return tag as a string

-- getFullIdx :: Integral a => Int -> [Char] -> a -> [Char]
getFullIdx idx cacheType bitsnum
  | cacheType /= "fullyAssoc" = fillZeros index (bitsnum - length index)
  | otherwise = ""
  where
    index = show idx

getEffectiveAddress :: Int -> Int -> [Char] -> Int -> [Char]
getEffectiveAddress tag idx cacheType bitsnum = getFullTag tag cacheType bitsnum ++ getFullIdx idx cacheType bitsnum

replaceInCache :: Integral b => Int -> Int -> [a] -> [Item a] -> [Char] -> b -> (a, [Item a])
replaceInCache tag idx memory oldCache "directMap" bitsNum = (d, updateCache)
  where
    updateCache = replaceIthItem newItem oldCache (convertBinToDec idx)
    -- newCache = incrementOrder oldCache
    newItem = (It (T tag) (D d) True 0)
    d = memory !! address
    address = convertBinToDec binAddress
    binAddress = read (getEffectiveAddress tag idx "directMap" (fromIntegral bitsNum)) :: Int
replaceInCache tag idx memory oldCache "fullyAssoc" bitsNum = (d, updatedCache)
  where
    updatedCache = replaceIthItem newItem (incrementOrder oldCache) (replaceIdx)
    replaceIdx = if invIdx == ((length oldCache)) then maxIdx else (invIdx)
    invIdx = getFirstInvIdx oldCache
    maxIdx = getMaxIndex oldCache
    -- (Just itemIdx) = firstNth0 oldCache (It (T _) (D _) False _)
    -- maxIdx = firstNth0 oldCache (It (T _) (D _) _ max)
    -- maxOrder = getMaxOrder oldCache
    newItem = (It (T tag) (D d) True 0)
    d = memory !! address
    address = convertBinToDec binAddress
    binAddress = read (getEffectiveAddress tag idx "fullyAssoc" (fromIntegral bitsNum)) :: Int
replaceInCache tag idx memory oldCache "setAssoc" bitsNum = (d, finalCache)
  where
    finalCache = appendSplitted updatedCache
    updatedCache = replaceIthItem updatedSet splittedCache idx
    updatedSet = replaceIthItem newItem (incrementOrder (splittedCache !! idx)) (replaceIdx)
    replaceIdx = if invIdx == ((length splittedCache)) then maxIdx else (invIdx)
    invIdx = getFirstInvIdx (splittedCache !! idx)
    maxIdx = getMaxIndex (splittedCache !! idx)
    splittedCache = splitEvery (div (length oldCache) (2 ^ bitsNum)) oldCache
    newItem = (It (T tag) (D d) True 0)
    d = memory !! address
    address = convertBinToDec binAddress
    binAddress = read (getEffectiveAddress tag idx "setAssoc" (fromIntegral bitsNum)) :: Int

getData :: (Eq t, Integral b) => String -> [Item t] -> [t] -> [Char] -> b -> (t, [Item t])
getData stringAddress cache memory cacheType bitsNum
  | x == NoOutput = replaceInCache tag index memory cache cacheType bitsNum
  | otherwise = (getX x, cache)
  where
    x = getDataFromCache stringAddress cache cacheType bitsNum
    address = read stringAddress :: Int
    (tag, index) = convertAddress address bitsNum cacheType
    getX (Out (d, _)) = d

runProgram :: (RealFloat a1, Eq a2) => [[Char]] -> [Item a2] -> [a2] -> [Char] -> a1 -> ([a2], [Item a2])
runProgram [] cache _ _ _ = ([], cache)
runProgram (addr : xs) cache memory cacheType numOfSets = ((d : prevData), finalCache)
  where
    bitsNum = round (logBase2 numOfSets)
    (d, updatedCache) = getData addr cache memory cacheType bitsNum
    (prevData, finalCache) = runProgram xs updatedCache memory cacheType numOfSets