# keep only one of
# part0.Booleans.md.645._∨𝔹_
# part0.Booleans.md.645.∨𝔹

BEGIN { FS=" ";}
/^.*/ {
    
    if ($1 == mykey)
        print $1 $2 $3;
    
    next;
}

END {

    print "Passed var " mykey

}