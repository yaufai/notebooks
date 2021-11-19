import time
import threading

def wait_one_sec(i):
    time.sleep(1)

data = range(10)

# マルチスレッドを利用しない場合

time_start = time.time()

for i in data:
    wait_one_sec(i)

print("マルチスレッドなし: ", time.time() - time_start)


# マルチスレッドを利用する場合

time_start = time.time()

threads = []

for i in data:
    thread = threading.Thread(target=wait_one_sec, args=(i,))
    thread.start()
    threads.append(thread)

for thread in threads:
    thread.join()

print("マルチスレッドあり: ", time.time() - time_start)


# $ python3 basic-time-measure.py 
# マルチスレッドなし:  10.012403964996338
# マルチスレッドあり:  1.005929708480835