/**
 * @file Multiprocessing.hpp
 * Defines class Multiprocessing.
 */

#ifndef __Multiprocessing__
#define __Multiprocessing__

#include "Forwards.hpp"
#ifdef _WIN32

#define _NSIG           64
#define SIGHUP           1
#define SIGINT           2
#define SIGQUIT          3
#define SIGILL           4
#define SIGTRAP          5
#define SIGABRT          6
#define SIGIOT           6
#define SIGBUS           7
#define SIGFPE           8
#define SIGKILL          9
#define SIGUSR1         10
#define SIGSEGV         11
#define SIGUSR2         12
#define SIGPIPE         13
#define SIGALRM         14
#define SIGTERM         15
#define SIGSTKFLT       16
#define SIGCHLD         17
#define SIGCONT         18
#define SIGSTOP         19
#define SIGTSTP         20
#define SIGTTIN         21
#define SIGTTOU         22
#define SIGURG          23
#define SIGXCPU         24
#define SIGXFSZ         25
#define SIGVTALRM       26
#define SIGPROF         27
#define SIGWINCH        28
#define SIGIO           29
#define SIGPOLL         SIGIO
 /*
 #define SIGLOST         29
 */
#define SIGPWR          30
#define SIGSYS          31
#define SIGUNUSED       31

 /* These should not be considered constants from userland.  */
#define SIGRTMIN        32
#ifndef SIGRTMAX
#define SIGRTMAX        _NSIG
#endif

#else
#include <unistd.h>
#endif

namespace Lib {
namespace Sys {

class Multiprocessing {
public:
  static Multiprocessing* instance();

  pid_t waitForChildTermination(int& resValue);
  pid_t waitForChildTerminationOrTime(unsigned timeMs,int& resValue);
  void waitForParticularChildTermination(pid_t child, int& resValue);

  pid_t fork();
  void registerForkHandlers(VoidFunc before, VoidFunc afterParent, VoidFunc afterChild);

  void sleep(unsigned ms);
  void kill(pid_t child, int signal);
  void killNoCheck(pid_t child, int signal);
  pid_t poll_children(bool &stopped, bool &exited, bool &signalled, int &code);
private:
  Multiprocessing();
  ~Multiprocessing();

  static void executeFuncList(VoidFuncList* lst);

  VoidFuncList* _preFork;
  VoidFuncList* _postForkParent;
  VoidFuncList* _postForkChild;
};

}
}

#endif // __Multiprocessing__
