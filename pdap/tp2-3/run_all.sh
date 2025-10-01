echo "" > log.log

python smpi-generate-ring.py 32 100 100 100Gbps 1us
smpirun -hostfile ring-32-hostfile.txt -platform ring-32-platform.xml ./bcast default_bcast >> log.log
python smpi-generate-ring.py 32 100 100 100Gbps 10us
smpirun -hostfile ring-32-hostfile.txt -platform ring-32-platform.xml ./bcast default_bcast >> log.log
python smpi-generate-ring.py 32 100 100 100Gbps 100us
smpirun -hostfile ring-32-hostfile.txt -platform ring-32-platform.xml ./bcast default_bcast >> log.log

python smpi-generate-ring.py 32 100 100 100Gbps 1us
smpirun -hostfile ring-32-hostfile.txt -platform ring-32-platform.xml ./bcast naive_bcast >> log.log
python smpi-generate-ring.py 32 100 100 100Gbps 10us
smpirun -hostfile ring-32-hostfile.txt -platform ring-32-platform.xml ./bcast naive_bcast >> log.log
python smpi-generate-ring.py 32 100 100 100Gbps 100us
smpirun -hostfile ring-32-hostfile.txt -platform ring-32-platform.xml ./bcast naive_bcast >> log.log

python smpi-generate-ring.py 32 100 100 100Gbps 1us
smpirun -hostfile ring-32-hostfile.txt -platform ring-32-platform.xml ./bcast ring_bcast >> log.log
python smpi-generate-ring.py 32 100 100 100Gbps 10us
smpirun -hostfile ring-32-hostfile.txt -platform ring-32-platform.xml ./bcast ring_bcast >> log.log
python smpi-generate-ring.py 32 100 100 100Gbps 100us
smpirun -hostfile ring-32-hostfile.txt -platform ring-32-platform.xml ./bcast ring_bcast >> log.log

for CHUNK_SIZE in 1000000 10000000 25000000 50000000 100000000
do
python smpi-generate-ring.py 32 100 100 100Gbps 1us
smpirun -hostfile ring-32-hostfile.txt -platform ring-32-platform.xml ./bcast pipelined_ring_bcast -c $CHUNK_SIZE >> log.log
python smpi-generate-ring.py 32 100 100 100Gbps 10us
smpirun -hostfile ring-32-hostfile.txt -platform ring-32-platform.xml ./bcast pipelined_ring_bcast -c $CHUNK_SIZE >> log.log
python smpi-generate-ring.py 32 100 100 100Gbps 100us
smpirun -hostfile ring-32-hostfile.txt -platform ring-32-platform.xml ./bcast pipelined_ring_bcast -c $CHUNK_SIZE >> log.log
done


for CHUNK_SIZE in 1000000 10000000 25000000 50000000 100000000
do
python smpi-generate-ring.py 32 100 100 100Gbps 1us
smpirun -hostfile ring-32-hostfile.txt -platform ring-32-platform.xml ./bcast asynchronous_pipelined_ring_bcast -c $CHUNK_SIZE >> log.log
python smpi-generate-ring.py 32 100 100 100Gbps 10us
smpirun -hostfile ring-32-hostfile.txt -platform ring-32-platform.xml ./bcast asynchronous_pipelined_ring_bcast -c $CHUNK_SIZE >> log.log
python smpi-generate-ring.py 32 100 100 100Gbps 100us
smpirun -hostfile ring-32-hostfile.txt -platform ring-32-platform.xml ./bcast asynchronous_pipelined_ring_bcast -c $CHUNK_SIZE >> log.log
done

for CHUNK_SIZE in 1000000 10000000 25000000 50000000 100000000
do
python smpi-generate-ring.py 32 100 100 100Gbps 1us
smpirun -hostfile ring-32-hostfile.txt -platform ring-32-platform.xml ./bcast asynchronous_pipelined_bintree_bcast -c $CHUNK_SIZE >> log.log
python smpi-generate-ring.py 32 100 100 100Gbps 10us
smpirun -hostfile ring-32-hostfile.txt -platform ring-32-platform.xml ./bcast asynchronous_pipelined_bintree_bcast -c $CHUNK_SIZE >> log.log
python smpi-generate-ring.py 32 100 100 100Gbps 100us
smpirun -hostfile ring-32-hostfile.txt -platform ring-32-platform.xml ./bcast asynchronous_pipelined_bintree_bcast -c $CHUNK_SIZE >> log.log
done
