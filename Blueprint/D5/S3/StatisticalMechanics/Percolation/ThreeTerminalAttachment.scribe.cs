using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Percolation;

internal sealed class ThreeTerminalAttachmentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Percolation/ThreeTerminalAttachment.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An independent attachment at any terminal preserves a strengthened "
            + "three-terminal determinant estimate for every constant at least one.",
        H("Attachment and the strengthened determinant invariant"),
        Blocks(
            Node("Port", "The three terminal labels", DescribeRole.Definition,
                "Port has exactly three values a,b,c and specifies the terminal "
                    + "whose connection to its original network is independently retained."),
            Node("detach", "Deterministic terminal partition map", DescribeRole.Definition,
                "For a port, a five-partition mode and a Boolean bit, detach keeps "
                    + "the mode when the bit is true. For a false bit it separates "
                    + "that labelled terminal from its former block: all becomes bc, "
                    + "ac or ab when port a, b or c is detached, respectively; the "
                    + "pair not involving the detached label is retained, and every "
                    + "other mode becomes separate."),
            Node("transfer", "Independent product source", DescribeRole.Definition,
                "For a port, mode weights p, real number q and output mode s, "
                    + "transfer is the sum over every input mode t and Boolean bit "
                    + "of p(t) times the Bernoulli weight q or 1-q, restricted to "
                    + "detach(port,t,bit)=s. Thus a normalized nonnegative p and "
                    + "q in [0,1] give the actual finite independent product pushforward. "
                    + "Its five entry formulas are derived from this source."),
            Node("attachment_invariant", "Closure at all three terminals", DescribeRole.Theorem,
                "For every nonnegative normalized five-mode source p, real C at "
                    + "least one, q in [0,1], and delta(p)>=0 with "
                    + "delta(p)+p(all)*p(ac)<=C*p(ac), every port's transfer r satisfies "
                    + "delta(r)>=0 and delta(r)+r(all)*r(ac)<=C*r(ac). Put T=p(all), "
                    + "Z=p(ac), N=p(separate), A=p(ab), B=p(bc). At either outer "
                    + "terminal delta(r)=q*delta(p)+q*(1-q)*T*Z and the strengthened "
                    + "left side equals q*(delta(p)+T*Z). At the middle terminal "
                    + "delta(r)=q^2*delta(p)+q*(1-q)*T*(N+A+B). Normalization gives "
                    + "the strengthened left side q^2*(delta(p)+T*Z)+q*(1-q)*T. "
                    + "Use q^2<=1 and q<=C to bound it by C*(Z+(1-q)*T). These "
                    + "are identities of the same product pushforward; no division "
                    + "by a mode mass or by q occurs, and all boundary rates are included."),
            Node("attachment_signed_invariant", "Closure for an absolute determinant bound", DescribeRole.Theorem,
                "For every nonnegative normalized five-mode source p, real C>=1, q in [0,1], "
                    + "and |delta(p)|+p(all)*p(ac)<=C*p(ac), every port's actual transfer r "
                    + "satisfies |delta(r)|+r(all)*r(ac)<=C*r(ac), without a sign assumption "
                    + "on delta(p). The same exact determinant identities as in attachment_invariant "
                    + "have nonnegative remainder terms. The triangle inequality bounds the "
                    + "outer-port strengthened quantity by q*(|delta(p)|+p(all)*p(ac)); "
                    + "normalization bounds the middle-port quantity by "
                    + "q^2*(|delta(p)|+p(all)*p(ac))+q*(1-q)*p(all). Boundary rates and "
                    + "zero mode masses are included. joined_network_signed_invariant consumes "
                    + "this result for an actual independent network substituted at one gate.")),
        []));

    private static DocumentBlock Node(string name, string title, DescribeRole role, string text) =>
        Describe.Lean(DescribeId.Create("three-terminal-attachment-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
}
