
import time

class TakeTime:

    def __init__(self):
        self.start= time.time()
        self.last = self.start

    def print_tdiff(self,s,tf=True):
        if tf:
            now = time.time()
            diff = (now - self.last)
            print (s+": %0.4f seconds" % diff)
            self.last=now

    def time_passed(self):
        now = time.time()
        diff = (now - self.start)/1000
