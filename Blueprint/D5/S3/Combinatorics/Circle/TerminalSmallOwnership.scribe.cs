using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class TerminalSmallOwnershipDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Terminal SMALL ownership prefix for an arbitrary physical signed source word.",
        H("Terminal SMALL ownership prefix"),
        Blocks(
            Paragraph(Text("For the actual physical source s(k,t), retain every occurrence in the literal word W=F++[z]++E. The prefix theorem assumes k>=3, p is positive, n=hit(k,1,p) is a native negative LARGE, z is a negative LARGE, E consists of SMALL occurrences, p and n are fresh in the whole W, and W is a Legal global J minimum among all Legal physical words.")),
            Describe.Lean(DescribeId.Create("terminal-small-ownership-prefix"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/TerminalSmallOwnership.actualSource_terminal_small_ownership_prefix"),
                H("Forced endpoint corridor and nonnegative SMALL ownership"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Writing P=s(p), D=|s(n)|, B=C-P, d=P-D, u=mass(s,F), and q(m)=mass(s,F++[z]++E.take(m)), the theorem proves C-d<u and B<q(m)<D for every natural m, including saturated takes. Each inequality is forced by a literal Legal competitor: a low prefix receives the fresh pair [p,n], while a high prefix receives the fresh n; the returned suffix remains an actual suffix of the original physical word.")),
                    Paragraph(Text("The source geometry supplies D=2B+1 and the exact native ordering and budget. All physical labels remain Fin(k) occurrences. The proof does not identify equal source values, assume numerical injectivity, or replace the original signed F by a scalar profile. The inventory balances are obtained from the existing physical permutation API.")),
                    Paragraph(Text("Every physical i with |s(i)|<Q and s(i)>=0 must already occur in W. If appending i at the old terminal height is legal, U strictly decreases. If it fails, the literal competitor F++[z]++[i,n] is Legal and uses the fresh LARGE n; its mixed SMALL/LARGE accounting is derived through a baseline word W++[i], preserving all physical occurrences and strictly lowering G. This is a genuine ownership result, while the unused negative SMALL orbit and the remaining two-step transition are left open.")),
                    Paragraph(Text("This prefix does not prove the full terminal-small telescope or Circle C3.1. In particular, no conclusion is asserted for an unused negative SMALL, its successor orbit, or a global disjoint resource partition after that orbit enters already-used labels."))),
                DescribeRole.Theorem)), []));
}
