import Prelude

printStars::Int -> IO ()
printStars n = sequence_ $ replicate n (putStr "*")

printUserStars :: IO ()
printUserStars = do {
    ln <- readLn;
    printStars ((read ln) * 5);
}

opNTimes::Int -> IO ()
opNTimes 0 = return ()
opNTimes n = do {
                 putStr ".";
                 opNTimes (n-1)
               }

operateAfter::IO () -> IO () -> IO ()
operateAfter op1 op2 = do {op1; op2}
