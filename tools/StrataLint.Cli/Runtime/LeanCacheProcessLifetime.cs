using StrataLint.Engine;

namespace StrataLint.Cli;

// The cache command owns a POSIX session. Its existing lock files retain the
// session ID until every descendant exits, even if .NET or Lake dies. This is a kernel
// liveness check, with no expiry, service, lease or assumption that Lean inherits fds.
internal static class LeanCacheProcessLifetime
{
    private const string Launcher = """
        use strict; use warnings; use POSIX qw(setsid); use Fcntl qw(:flock F_SETFD FD_CLOEXEC);
        my $count = shift @ARGV;
        my @guards;
        for (1 .. $count) {
            my $fd = shift @ARGV;
            open(my $guard, '+<&=', $fd) or die "cache guard was not inherited: $!";
            flock($guard, LOCK_EX | LOCK_NB) or die "cache guard ownership lost: $!";
            push @guards, $guard;
        }
        setsid() > 0 or die "cannot establish cache writer session: $!";
        for my $guard (@guards) {
            sysseek($guard, 0, 0) == 0 or die "cache guard seek: $!";
            my $record = "$$\n";
            syswrite($guard, $record) == length($record) or die "cache guard write: $!";
            truncate($guard, length($record)) or die "cache guard truncate: $!";
            fcntl($guard, F_SETFD, FD_CLOEXEC) or die "cache guard close-on-exec: $!";
        }
        exec { $ARGV[0] } @ARGV or die "cache command exec: $!";
        """;

    internal static ProcessOutput Run(IWorktreeProcessRunner runner, string file, IReadOnlyList<string> arguments,
        string root, TimeSpan timeout, IReadOnlyDictionary<string, string> environment,
        IReadOnlyList<LeanCacheWriterGuard> writers)
    {
        if (writers.Count == 0 || OperatingSystem.IsWindows())
            return runner.RunWithEnvironment(file, arguments, root, timeout, environment);
        if (!File.Exists("/usr/bin/perl"))
            throw new PlatformNotSupportedException("Cache writer process ownership requires /usr/bin/perl on POSIX.");
        var guards = writers.Select(writer => writer.ProcessGuard).ToArray();
        foreach (var guard in guards)
            if (guard.HasWriterSession())
                throw new InvalidOperationException("cache command still has writer descendants; writer guard is busy");
        var previous = BoundedProcessRunner.StartProcess.Value;
        BoundedProcessRunner.StartProcess.Value = process =>
        {
            try
            {
                foreach (var guard in guards) guard.SetInheritable(true);
                return previous?.Invoke(process) ?? process.Start();
            }
            finally
            {
                foreach (var guard in guards) guard.SetInheritable(false);
            }
        };
        try
        {
            var result = runner.RunWithEnvironment("/usr/bin/perl",
                ["-e", Launcher, guards.Length.ToString(System.Globalization.CultureInfo.InvariantCulture),
                    .. guards.Select(guard => guard.Descriptor.ToString(System.Globalization.CultureInfo.InvariantCulture)),
                    file, .. arguments], root, timeout, environment);
            foreach (var guard in guards)
                if (guard.HasWriterSession())
                    throw new InvalidOperationException("cache command exited with live writer descendants; writer guard remains busy");
            // Normal completion needs no stale session lookup at the next command.
            // Crashes and exceptions retain the reservation for the next owner to inspect.
            foreach (var guard in guards) guard.ClearExitedSession();
            return result;
        }
        finally { BoundedProcessRunner.StartProcess.Value = previous; }
    }
}
