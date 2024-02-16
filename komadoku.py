# -*- coding: utf-8 -*-
"""
Created on Mon Aug 14 08:50:39 2023

@author: sammy
"""

komaten=[15000,540,990,855,495,405,315,90,1395,945,540,540,540,540]
def output(i):
    if(i%28<=13):
        return 2282
    else:
        return 2284
def captured_output(i):
    if((i-2268)%7<=6):
        return 2282
    else:
        return 2284
      
def weight(i):
    r = i%14
    return komaten[r]*0.9
def captured_weight(i):
    r = (i-2268)%7
    if r == 0:
        return komaten[2]
    elif r == 1:
        return komaten[3]
    elif r == 2:
        return komaten[1]
    else:
        return komaten[r+1]

f = open('komadoku.txt','w')
f.write('nodes\n')
for i in range(2282):
    f.write(f'sensor {i} {i}\n')
for i in range(3):
    f.write(f'output {i+2282} {i+2282}\n')
f.write('\nconnection\n') 
for i in range(2268):
    f.write(f'{i} {i} {i} {output(i)} {output(i)} {weight(i)} true\n')
for i in range(14):
    f.write(f'{i+2268} {i+2268} {i+2268} {output(i)} {captured_output(i)} {float(captured_weight(i))} true\n')


