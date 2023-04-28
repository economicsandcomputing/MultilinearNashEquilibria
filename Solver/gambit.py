import gambit
import pygambit
import time
import signal
import sys

class TimeoutException(Exception):   # Custom exception class
    pass

def timeout_handler(signum, frame):   # Custom signal handler
    raise TimeoutException

# Change the behavior of SIGALRM
signal.signal(signal.SIGALRM, timeout_handler)

#g = gambit.Game.read_game("/Users/miriamfischer/Desktop/Output/Games/CG_multi_3_10_10.nfg")
#solvergam = gambit.nash.ExternalSimpdivSolver()

#Simpdiv GlobalNewton Logit 

with open("/Users/miriamfischer/Desktop/Output/function/CG_5_10_Simplicial.log", "a") as file:
    for i in range(10):
        filename = "/Users/miriamfischer/Desktop/Output/Games/CG_multi_5_10_" + str(i+1) + ".nfg"
        g = gambit.Game.read_game(filename)
        solvergam = gambit.nash.ExternalSimpdivSolver()
        #g = pygambit.Game.read_game(filename)
        #solvergam = pygambit.nash.ExternalGlobalNewtonSolver()
        signal.alarm(900) 
        t1 = time.time()
        try:
            eq = solvergam.solve(g) # solve game
        except TimeoutException:
            t2 = time.time() - t1 
            print("CG 5_10_" + str(i+1), file=file)
            print(f"Timeout(in seconds) {t2:.2f}", file=file)
            print("", file=file)
            print("", file=file)
            print(f"Time(in seconds) {t2:.2f}")
        else:
            # Reset the alarm
            signal.alarm(0)
            t2 = time.time() - t1
            print("CG 5_10_" + str(i+1), file=file)
            print(eq, file=file)
            print(f"Time(in seconds) {t2:.2f}", file=file)
            print("", file=file)
            print("", file=file)
            print(eq)
            print(f"Time(in seconds) {t2:.2f}")
        signal.alarm(0)

