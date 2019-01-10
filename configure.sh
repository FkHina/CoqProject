
# We sort files, because coqdep sometimes don't like unorderedfiles.
# We also remove inherit.v

echo "-Q . bcv" > _CoqProject
coqdep -Q . bcv -sort *.v -exclude-dir projet-tp | sed -e "s/ /\n/g" | sed -e "s/\.vo/\.v/" | grep -v inherit >> _CoqProject

coq_makefile -f _CoqProject -o Makefile

# If coq version is pre 8.7, then Makefile.local is not loaded by the
# Makefile, so we insert a -include
if coqc -v | grep 8.6 ;
then
    echo v8.6
    COQVERSION=v8.6
    sed -i -e "s/\(Makefile: _CoqProject\)/\-include Makefile.local_v86\n\1/" Makefile
else
    echo autre version
fi
