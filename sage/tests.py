import sage.all

def cnd (x):
    return cos(pi/180*x) + I*sin(pi/180*x)

def cn (x):
    return cos(x) + I*sin(x)


a=cnd(37)
b=cnd(47)
c=cnd(301)

def sumpow(es,i):
    p= map(lambda x:n(x**i),es)
    sp=abs(sum(p))
    return (p,sp)

prev1=0
prev2=0
smallest=3
for i in range(1000):
    r = sumpow([a,b,c],i)[1]

    if prev2+prev1+r < smallest:
        smallest = prev2+prev1+r
        print i,r,prev1,prev2,prev2+prev1+r
    prev2=prev1
    prev1=r

def one_step(cnums):
    angles=map(arg,cnums)
    print map(n,angles)
    distrib_angle=2*pi/len(cnums)
    print distrib_angle
    distrib_angles=map(lambda x:distrib_angle*x,range(0,len(cnums)))
    print distrib_angles
    zerocnums=map(cn,distrib_angles)
    print zerocnums
    stepcnums=map(lambda x:x[0]+x[1],zip(angles,zerocnums))
    return stepcnums
