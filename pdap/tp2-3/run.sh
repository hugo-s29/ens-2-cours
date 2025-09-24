python smpi-generate-ring.py 32 100 100 100Gbps 1us
smpirun -hostfile ring-32-hostfile.txt -platform ring-32-platform.xml ./bcast asynchronous_pipelined_ring_bcast -c $CHUNK_SIZE
python smpi-generate-ring.py 32 100 100 100Gbps 10us
smpirun -hostfile ring-32-hostfile.txt -platform ring-32-platform.xml ./bcast asynchronous_pipelined_ring_bcast -c $CHUNK_SIZE
python smpi-generate-ring.py 32 100 100 100Gbps 100us
smpirun -hostfile ring-32-hostfile.txt -platform ring-32-platform.xml ./bcast asynchronous_pipelined_ring_bcast -c $CHUNK_SIZE
