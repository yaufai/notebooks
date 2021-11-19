import time, threading, queue

def do_experiment(max_size):
    data = range(10)

    q = queue.Queue(maxsize=max_size)


    def wait_one_sec(queue_obj):
        item = queue_obj.get()
        time.sleep(1)
        queue_obj.task_done()

    time_start = time.time()


    for i in data:
        thread = threading.Thread(target=wait_one_sec, args=(q,))
        thread.start()
        q.put(i)

        if threading.active_count() >= max_size + 1:
            q.join()


    print("サイズ" + str(max_size) + ": ", time.time() - time_start)


do_experiment(1)
do_experiment(2)
do_experiment(5)

# $ python3 use-queue-maximum.py 
# サイズ1:  10.020220518112183
# サイズ2:  5.010011434555054
# サイズ5:  2.0056521892547607