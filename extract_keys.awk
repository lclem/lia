
# part0.Booleans.html#216 part0.Booleans.md#1841 tt

BEGIN { FS=" ";}
/^.*/ {
    
    if ($1 == mykey)
        print $1 $2 $3;
    
    next;
}

END {

    print "Passed var " mykey

}