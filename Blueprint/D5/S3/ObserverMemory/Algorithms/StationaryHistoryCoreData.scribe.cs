using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class StationaryHistoryCoreDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual core data from original controller targets.",
        H("StationaryHistoryCoreData"),
        Blocks(
            Result("actual_core_data", "actual-core-data", "Unrestricted original structural interface",
                Scope(Instances(At("CoreData"), Call("Fintype", V("Q")))),
                "CoreData collects the proved actual incidence, degree, two-row, production and resolving "
                + "counts, selected-target count and outside-B property, target identities and distinct "
                + "resolving rows, s<=J, pure unary structure, N core and e extra targets, and the original "
                + "ActualRead cardinal N+1+e. It also contains the disjoint exact target partition, strict "
                + "binary representative bound, exact binary/selected-literal baseline assignments, all "
                + "actual tail bounds, core digit occupancy, absence of extra background, and indexed "
                + "history separation. This is the structural input to the subsequent weighted inventory; "
                + "it states no overlap correction, weighted necessary inequality, zero-correction theorem, "
                + "synthesis, or global capacity conclusion."))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula At(string name, params Formula[] args) =>
        Call(name, [V("C"), V("hP"), V("I"), .. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, type, Comma, Grp(body));
    private static Formula Instances(Formula body, params Formula[] types) =>
        Seq([.. types.Select(t => Seq(OpenBracket, t, CloseBracket)), body]);
    private static Formula Scope(Formula body) => All("P", Nat, All("Q", Seq(V("Type"), Underscore, Grp(V("u"))),
        Instances(All("C", Call("Controller", V("P"), V("Q")),
        All("hP", Seq(D(1), Lt, V("P")), All("ell", Nat, All("h", Nat,
        All("I", Call("Initialized", V("C"), V("hP"), V("ell"), V("h")), body))))),
        Call("DecidableEq", V("Q")), Call("NeZero", Seq(D(3), Times, Sp, V("P"))))));
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Sp, Grp(V(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static DocumentBlock ResultAt(string owner, string declaration, string id, string title,
        Formula statement, string explanation) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/" + owner + "." + declaration),
        H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);

    private static DocumentBlock Result(string declaration, string id, string title,
        Formula statement, string explanation) => ResultAt("StationaryHistoryCoreData", declaration, id, title, statement, explanation);
}
