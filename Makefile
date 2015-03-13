#
# Students' Makefile for the Malloc Lab
#
TEAM = $(shell egrep '^ *\* *Group:' mm.c | sed -e 's/\*//g' -e 's/ *Group: *//g' | sed 's/ *\([^ ].*\) *$$/\1/g')
USER_1 = $(shell egrep '^ *\* *User 1:' mm.c | sed -e 's/\*//g' -e 's/ *User 1: *//g' | sed 's/ *\([^ ].*\) *$$/\1/g')
USER_2 = $(shell egrep '^ *\* *User 2:' mm.c | sed -e 's/\*//g' -e 's/ *User 2: *//g' | sed 's/ *\([^ ].*\) *$$/\1/g')

ifeq "$(TEAM)" ""
	TEAM = "NONE"
endif
ifeq "$(USER_1)" ""
	USER_1 = "NONE"
endif
ifeq "$(USER_2)" ""
	USER_2 = "NONE"
endif

VERSION = 1
HANDINDIR = /labs/sty15/.handin/malloclab

CC = gcc
CFLAGS = -Wall -ggdb3 -m32

OBJS = mdriver.o mm.o memlib.o fsecs.o fcyc.o clock.o ftimer.o

mdriver: $(OBJS)
	$(CC) $(CFLAGS) -o mdriver $(OBJS)

mdriver.o: mdriver.c fsecs.h fcyc.h clock.h memlib.h config.h mm.h
memlib.o: memlib.c memlib.h
mm.o: mm.c mm.h memlib.h
fsecs.o: fsecs.c fsecs.h config.h
fcyc.o: fcyc.c fcyc.h
ftimer.o: ftimer.c ftimer.h config.h
clock.o: clock.c clock.h

handin:
	@echo "Team: \"$(TEAM)\""
	@echo "User 1: \"$(USER_1)\""
	@echo "User 2: \"$(USER_2)\""
	@if [ "$(TEAM)" == "NONE" ]; then echo "Team name missing, please add it to the mm.c file."; exit 1; fi
	@if [ "$(USER_1)" != "NONE" ]; then getent passwd $(USER_1) > /dev/null; if [ $$? -ne 0 ]; then echo "User $(USER_1) does not exist on Skel."; exit 2; fi; fi
	@if [ "$(USER_2)" != "NONE" ]; then getent passwd $(USER_2) > /dev/null; if [ $$? -ne 0 ]; then echo "User $(USER_2) does not exist on Skel."; exit 3; fi; fi
	cp mm.c "$(HANDINDIR)/$(USER)/$(TEAM)-$(VERSION)-mm.c"
	@chmod 600 "$(HANDINDIR)/$(USER)/$(TEAM)-$(VERSION)-mm.c"

clean:
	rm -f *~ *.o mdriver


