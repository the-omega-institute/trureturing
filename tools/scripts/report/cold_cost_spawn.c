/* Temporary process-launch observer. No toolchain paths or source files change. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <spawn.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

extern char **environ;

static int enabled(const char *path, char *const argv[], char *const envp[]) {
    const char *base = strrchr(path, '/');
    if (strcmp(base ? base + 1 : path, "lean") != 0) return 0;
    if (!getenv("COLD_COST_PROGRAM") || !getenv("COLD_COST_PYTHON")) return 0;
    for (size_t i = 0; envp && envp[i]; ++i)
        if (strcmp(envp[i], "COLD_COST_INTERNAL=1") == 0) return 0;
    int source = 0;
    for (size_t i = 1; argv[i]; ++i) {
        if (strcmp(argv[i], "--run") == 0) return 0;
        size_t n = strlen(argv[i]);
        if (n >= 5 && strcmp(argv[i] + n - 5, ".lean") == 0) source = 1;
    }
    return source;
}

static char **observer_argv(char *const argv[]) {
    size_t count = 0;
    while (argv[count]) ++count;
    char **args = calloc(count + 3, sizeof(char *));
    if (!args) return NULL;
    args[0] = getenv("COLD_COST_PYTHON");
    args[1] = getenv("COLD_COST_PROGRAM");
    args[2] = "compiler";
    for (size_t i = 1; i < count; ++i) args[i + 2] = argv[i];
    return args;
}

int posix_spawn(pid_t *pid, const char *path, const posix_spawn_file_actions_t *actions,
                const posix_spawnattr_t *attrs, char *const argv[], char *const envp[]) {
    typedef int (*Fn)(pid_t *, const char *, const posix_spawn_file_actions_t *, const posix_spawnattr_t *, char *const[], char *const[]);
    Fn original = (Fn)dlsym(RTLD_NEXT, "posix_spawn");
    if (!original) return ENOSYS;
    if (!enabled(path, argv, envp)) return original(pid, path, actions, attrs, argv, envp);
    char **args = observer_argv(argv);
    if (!args) return ENOMEM;
    int rc = original(pid, args[0], actions, attrs, args, envp);
    free(args);
    return rc;
}

int posix_spawnp(pid_t *pid, const char *path, const posix_spawn_file_actions_t *actions,
                 const posix_spawnattr_t *attrs, char *const argv[], char *const envp[]) {
    typedef int (*Fn)(pid_t *, const char *, const posix_spawn_file_actions_t *, const posix_spawnattr_t *, char *const[], char *const[]);
    Fn original = (Fn)dlsym(RTLD_NEXT, "posix_spawnp");
    if (!original) return ENOSYS;
    if (!enabled(path, argv, envp)) return original(pid, path, actions, attrs, argv, envp);
    char **args = observer_argv(argv);
    if (!args) return ENOMEM;
    int rc = original(pid, args[0], actions, attrs, args, envp);
    free(args);
    return rc;
}

int execve(const char *path, char *const argv[], char *const envp[]) {
    typedef int (*Fn)(const char *, char *const[], char *const[]);
    Fn original = (Fn)dlsym(RTLD_NEXT, "execve");
    if (!original) { errno = ENOSYS; return -1; }
    if (!enabled(path, argv, envp)) return original(path, argv, envp);
    char **args = observer_argv(argv);
    if (!args) { errno = ENOMEM; return -1; }
    int rc = original(args[0], args, envp);
    int saved = errno;
    free(args);
    errno = saved;
    return rc;
}

int execv(const char *path, char *const argv[]) { return execve(path, argv, environ); }

int execvp(const char *path, char *const argv[]) {
    typedef int (*Fn)(const char *, char *const[]);
    Fn original = (Fn)dlsym(RTLD_NEXT, "execvp");
    if (!original) { errno = ENOSYS; return -1; }
    if (!enabled(path, argv, environ)) return original(path, argv);
    char **args = observer_argv(argv);
    if (!args) { errno = ENOMEM; return -1; }
    int rc = original(args[0], args);
    int saved = errno;
    free(args);
    errno = saved;
    return rc;
}
