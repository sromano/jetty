#!/usr/bin/python

# not included in the repository
from ec2_keys import access_key, secret_access_key

import boto.ec2
import sys
import time
import os

machine_type = 'c3.8xlarge' #'r3.4xlarge'

build_target = sys.argv[1]
parameters = ""
p = 2
while p < len(sys.argv):
    parameters = parameters+" "+sys.argv[p]
    p = p+1

# file name under which saved the logs
name = build_target + parameters
name = name.replace(" ","_")
name = name.replace("/","_")

script_lines = """cd ~/
git clone https://github.com/ellisk42/jetty.git
cd ~/jetty
mkdir log
make %s
./test %s > log/output 2> log/errors
mv log %s
tar -czf %s.tgz %s
(uuencode %s.tgz %s.tgz ; cat %s/output) | mailx -s %s ellisk42@gmail.com
sudo shutdown -h now""" % (build_target, parameters, name, name, name, name, name, name, name)

script = ""
for l in script_lines.split("\n"):
    if len(script) > 0:
        script = script+"\necho \\\""+l+"\\\" >> collect_data_and_die"
    else:
        script = "\necho \\\""+l+"\\\" > collect_data_and_die"

if True:
    print "Launching instance..."

    c = boto.ec2.connect_to_region("us-east-1",aws_access_key_id = access_key,aws_secret_access_key = secret_access_key)

    i = c.run_instances('ami-ece24c84', key_name = 'eyal_ec2', instance_type = machine_type)
    i = i.instances[0]

    while not i.state == u'running':
        i.update()
        pass

    print "Running ",
    h = i.public_dns_name
    print h

    print "Waiting for a minute..."
    time.sleep(60)

# wrap the script so it will be executable
script = script+"\nchmod +x ~/collect_data_and_die\necho \\\". /home/ubuntu/.opam/opam-init/init.sh > /dev/null 2> /dev/null || true\\\" > rapper\necho \\\"nohup ~/collect_data_and_die > /dev/null 2>&1 &\\\" >> rapper\nchmod +x rapper"

print "Issuing command..."
command = "ssh -o StrictHostKeyChecking=no -i ~/key.pem ubuntu@%s \"%s\"" % (h, script)
os.system(command)

print "Waiting for 5 seconds before launching wrapper..."
time.sleep(5)
os.system("ssh -o StrictHostKeyChecking=no -i ~/key.pem ubuntu@%s \"~/rapper\"" % (h))
