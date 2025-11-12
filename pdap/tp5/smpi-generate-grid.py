#!/usr/bin/env python3
import sys

# Link parameters
link_latency = "10us"
link_bandwidth = 10
link_bandwidth_unit = "Gbps"

# XML generation functions
def issueHead():
        head = ("<?xml version='1.0'?>\n"
                "<!DOCTYPE platform SYSTEM \"http://simgrid.gforge.inria.fr/simgrid/simgrid.dtd\">\n"
                "<platform version=\"4.1\">\n\n")

        config_clause = ("<!--  WARNING:  This <config></config> clause below\n"
                       "makes it so that NO COMPUTATION TIME is simulated. This is because\n"
                       "in this module, for pedagogic purposes, we don't want to muddy the\n"
                       "(simulation) waters with computational times. As a results, this\n"
                       "XML platform file may not be suitable for running other\n"
                       "simulations, unless you remove the <config></config> clause.\n"
                       "-->\n"
                       "<config>\n"
                       "<prop id=\"smpi/simulate-computation\" value=\"1\"></prop>\n"
                       "<prop id=\"smpi/host-speed\" value=\""+str(real_compute_power)+"f\"></prop>\n"
                       "</config>\n\n")

        AS_head = "<zone id=\"AS0\" routing=\"Full\">\n"

        return head + config_clause + AS_head


def issueTail():
	return "</zone>\n</platform>\n"

def issueLink1(x):
	return "  <link id=\"link-"+str(x)+"\" latency=\""+str(link_latency)+"\" bandwidth=\""+link_bandwidth+"\"/>\n"

def issueLink2(x,y):
	return "  <link id=\"link-"+str(x)+"-"+str(y)+"\" latency=\""+str(link_latency)+"\" bandwidth=\""+link_bandwidth+"\"/>\n"

def issueLink3(x,y,bw):
	return "  <link id=\"link-"+str(x)+"-"+str(y)+"\" latency=\""+str(link_latency)+"\" bandwidth=\""+str(bw)+link_bandwidth_unit+"\"/>\n"

def issueHost(index):
	return "  <host id=\"host-"+str(index)+"."+hostname+"\" speed=\""+sim_compute_power+"\"/>\n"

def issueRouteHead(index1, index2):
	return "  <route src=\"host-"+str(index1)+"."+hostname+"\" dst=\"host-"+str(index2)+"."+hostname+"\">\n"
def issueRouteTail():
	return "  </route>\n"

def issueRouteLink1(x):
	return "\t<link_ctn id=\"link-"+str(x)+"\"/>\n"

def issueRouteLink2(x,y):
	return "\t<link_ctn id=\"link-"+str(x)+"-"+str(y)+"\"/>\n"

######################################################################
# Parse command-line arguments
if (len(sys.argv) != 6):
	print("Usage: smpi-generate-ring.py <num hosts> <real-machine-compute-power> <simulation-node-compute-power> <simulation-link-bandwidth> <simulation-link-latency> \n", file=sys.stderr)
	print("Example: smpi-generate-ring.py 32 1000 100 10Gbps 10us \n", file=sys.stderr)
	print("  Will generate a ring_<num hosts>.xml and hostfile_<num hosts>.txt file\n", file=sys.stderr)
	exit(1)

num_hosts = int(sys.argv[1])
sim_compute_power = sys.argv[2]+"Gf"
real_compute_power = int(sys.argv[3])*1000000000
link_bandwidth = sys.argv[4]
link_latency = sys.argv[5]
hostname = "nimportequoi.fr"

###############################################################
# Generate RING XML file
filename = "./grid-"+str(num_hosts)+"-platform.xml"
fh = open(filename, 'w')
fh.write(issueHead())

# Create hosts
for i in range(0,num_hosts):
	for j in range(0, num_hosts):
		fh.write(issueHost(i*num_hosts+j))

# Create links
for i in range(0,num_hosts):
	for j in range(0,num_hosts):
		if i<num_hosts-1:
			fh.write(issueLink2(i*num_hosts+j,(i+1)*num_hosts+j))
		if j<num_hosts-1:
			fh.write(issueLink2(i*num_hosts+j,i*num_hosts+j+1))

# Create routes
#for i in range (0,num_hosts):
#    for j in range(0,num_hosts):
#        for k in range(0,num_hosts):
#            if (i != k):
#                if (k > i):
#                    fh.write(issueRouteHead(i*num_hosts+j,k*num_hosts+j)) #Column links
#                    for l in range(i,k):
#                        fh.write(issueRouteLink2(l*num_hosts+j,(l+1)*num_hosts+j))
#                    fh.write(issueRouteTail())
#                else:
#                    for l in range(i-1,k-1,-1):
#                        fh.write(issueRouteLink2(l*num_hosts+j,(l+1)*num_hosts+j))
#            if (j != k):
#                if (k > j):
#                    fh.write(issueRouteHead(i*num_hosts+j,i*num_hosts+k)) #Row links
#                    for l in range(j,k):
#                        fh.write(issueRouteLink2(i*num_hosts+l,i*num_hosts+l+1))
#                    fh.write(issueRouteTail())
#                else:
#                    for l in range(j-1,k-1,-1):
#                        fh.write(issueRouteLink2(i*num_hosts+l,i*num_hosts+l+1))

for i in range(0,num_hosts):
	for j in range(0,num_hosts):
		for k in range(i,num_hosts):
			for l in range(0,num_hosts):
				if (k > i or (k==i and l>j)):
					fh.write(issueRouteHead(i*num_hosts+j,k*num_hosts+l))
					for ll in range(i,k):
						fh.write(issueRouteLink2(ll*num_hosts+j,(ll+1)*num_hosts+j))
					for ll in range (j,l):
						fh.write(issueRouteLink2(k*num_hosts+ll,k*num_hosts+ll+1))
					fh.write(issueRouteTail())

fh.write(issueTail())
fh.close()
print("Grid XML platform file created: "+filename)

###############################################################
## Generate host file
filename = "./grid-"+str(num_hosts)+"-hostfile.txt"
fh = open(filename, 'w')

for i in range(0,num_hosts):
	for j in range(0, num_hosts):
		fh.write("host-"+str(i*num_hosts+j)+"."+hostname+"\n")

fh.close()
print("Hostfile created: "+filename)
