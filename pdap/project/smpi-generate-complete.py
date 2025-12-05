#!/usr/bin/env python3
import sys

# Link parameters
link_latency = "10us"
link_bandwidth = 10
link_bandwidth_unit = "Gbps"


# XML generation functions
def issueHead():
  return f"""
<?xml version='1.0'?>
<!DOCTYPE platform SYSTEM "https://simgrid.org/simgrid.dtd">
<platform version="4.1">

<config>
	<prop id="smpi/host-speed" value="{real_compute_power}"></prop>
</config>

<zone id="AS0" routing="Dijkstra">
"""


def issueTail():
  return "</zone>\n</platform>\n"


def issueLink(x):
  return f"""\t<link id="link-{x}" latency="{link_latency}" bandwidth="{link_bandwidth}"/>\n"""


def issueHost(index):
  return f"""\t<host id="host-{index}.{hostname}" speed="{sim_compute_power}"/>\n"""


def issueRouteHead(index1, index2):
  return (
      f"""\t<route src="host-{index1}.{hostname}" dst="host-{index2}.{hostname}">\n"""
  )


def issueRouteTail():
  return "\t</route>\n"


def issueRouteLink(x):
  return f"""\t\t<link_ctn id="link-{x}"/>\n"""


######################################################################
# Parse command-line arguments
if len(sys.argv) != 6:
  print(
      "Usage: smpi-generate-complete.py <num hosts> <real-machine-compute-power> <simulation-node-compute-power> <simulation-link-bandwidth> <simulation-link-latency> \n",
      file=sys.stderr,
  )
  print("Example: smpi-generate-complete.py 32 1000 100 10Gbps 10us \n",
        file=sys.stderr)
  print(
      "  Will generate a platforms/complete-<num hosts>.xml and a hostfiles/complete-<num hosts>.txt file\n",
      file=sys.stderr,
  )
  exit(1)

num_hosts = int(sys.argv[1])
sim_compute_power = sys.argv[2] + "Gf"
real_compute_power = sys.argv[3] + "Gf"
link_bandwidth = sys.argv[4]
link_latency = sys.argv[5]
hostname = "simgrid.org"

###############################################################
# Generate COMPLETE XML file
filename = f"./platforms/complete-{num_hosts}.xml"
with open(filename, "w") as fh:
  fh.write(issueHead())

  # Create hosts
  for i in range(0, num_hosts):
    fh.write(issueHost(i))

  # Create links
  for i in range(0, num_hosts):
    fh.write(issueLink(i))

  # Create routes
  for i in range(0, num_hosts):
    for j in range(i + 1, num_hosts):
      fh.write(issueRouteHead(i, j))
      fh.write(issueRouteLink(i))
      fh.write(issueRouteLink(j))
      fh.write(issueRouteTail())

  fh.write(issueTail())

  print("Complete XML platform file created: " + filename, file=sys.stderr)

###############################################################
## Generate host file
filename = f"./hostfiles/complete-{num_hosts}.txt"

with open(filename, "w") as fh:
  for i in range(0, num_hosts):
    fh.write(f"host-{i}.{hostname}\n")

  print("Hostfile created: " + filename, file=sys.stderr)
