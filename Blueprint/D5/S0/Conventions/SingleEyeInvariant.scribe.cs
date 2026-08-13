using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Conventions;

internal sealed class SingleEyeInvariantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An observer is single-eyed at a coordinate when every admitted invariant depends only on that coordinate.",
        H("Single-Eyed Invariants"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("single-eyed-invariant"),
                DeclarationHandle.Create(
                    "D5/S0/Conventions/SingleEyeInvariant.IsSingleEyed"),
                H("Single-eyed observer predicate"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("invariant"), Sp, In(F.Id("admitted")), Comma, Sp,
                    Operatorname, Grp(F.Id("dependency")), Open,
                    F.Id("invariant"), Close, Sp, Subset, Sp,
                    OpenBrace, F.Id("coordinate"), CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary coordinate and invariant types, admitted is the set of "
                        + "invariants an observer accepts and dependency assigns each invariant its "
                        + "coordinate set. IsSingleEyed says every admitted dependency set is a "
                        + "subset of the singleton containing the selected coordinate.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies the singleton-subset interface used by this predicate, "
                        + "but no exact observer declaration was found in the library or repository. "
                        + "The Lean statement is therefore a direct generic encoding of the selected "
                        + "definition clause.")),
                    Paragraph(Text(
                        "This deposit is an honest partial closure of the leading definition clause of "
                        + "interface-philosophy-v4 corollary 4.5. Its later existence and visibility "
                        + "claims remain unresolved and are not asserted here."))),
                DescribeRole.Definition)),
        []));
}
