import time, threading, queue

data = range(10)

q = queue.Queue()


def wait_one_sec(queue_obj):
    item = queue_obj.get()
    time.sleep(1)
    queue_obj.task_done()

time_start = time.time()

for i in data:
    thread = threading.Thread(target=wait_one_sec, args=(q,))
    thread.start()
    q.put(i)

q.join()

print(time.time() - time_start) # -> 1.0044941902160645