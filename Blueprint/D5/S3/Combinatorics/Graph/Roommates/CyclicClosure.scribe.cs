using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Roommates;

internal sealed class CyclicClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six-site cyclic closure for the exact Mertens range-two proof.",
        H("Cyclic closure"), Blocks(
            Paragraph(Text("A word w of length m has a signed assignment d and Certificate(w,d). The source cycle has m+6 labelled sites, hence supplier parameter n=m+1. Assignment(m) means Fin(m) to the integers. SuccessfulProfile(n) is the subtype of SourceModel.Profile(n) admitting an acceptable stable partial matching. The matching keeps every interior old pair and old single, fulfills each actual exterior request, and uses the existing six-site buffer involution for free sites. The profile retains all first m rankings and places every nonzero buffer partner first.")),
            Describe.Lean(DescribeId.Create("matching"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.matching"),
                H("Actual involutive source matching"), StatementSource.FromAuthor(MatchingFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sum of the old interval and the six buffer vertices is identified with the labelled source cycle. Interior reciprocity is supplied by the certificate; the existing request involution supplies all exterior and new pairs. Fixed points represent singles."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("profile"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.profile"),
                H("The extended profile"), StatementSource.FromAuthor(ProfileFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every old ranking is retained literally. A buffer ranking is the existing partnerFirst permutation for its actual signed assignment, including the fixed deterministic ranking at a single."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("acceptable"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.acceptable"),
                H("Acceptable pairs and singles"), StatementSource.FromAuthor(AcceptableFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each assignment is zero or one of the four literal signed source offsets. Thus every nonfixed pair is an actual acceptable edge of the source ring."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("stable"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.stable"),
                H("No cyclic blocking edge"), StatementSource.FromAuthor(StableFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Old--old edges use the saved exact rank transport and have no new wrap edge. A matched buffer endpoint ranks its partner first and rejects any proposed improvement. A buffer single is at position 3 or 4 in one-based numbering; all four cyclic neighbors are distinct matched buffer vertices. This also excludes an edge from an old single to a new single. The argument includes m=1 and its extra edge between buffer positions 1 and 6, m=2, and odd m. There is no parity or eventual-length hypothesis."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("close"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.close"),
                H("Map on successful profiles"), StatementSource.FromAuthor(CloseFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose one certificate per certified word, construct its profile and stable matching, and retain only the successful profile. Certificates and matching witnesses are not counted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("close-injective"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.close_injective"),
                H("Recover the old ranking word"), StatementSource.FromAuthor(InjectiveFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Equality of output profiles gives equality at each first-m coordinate, recovering the input word independently of which certificate was chosen."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("count-le-successful-profile-count"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.count_le_successful_profile_count"),
                H("The lower cyclic count comparison"), StatementSource.FromAuthor(CountFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write b(m) for the number of certified ranking words, and a(n) for the number of successful labelled source profiles with supplier parameter n and n+5 sites. The injection proves b(m) <= a(m+1), equivalently b(m) <= a_(m+6) when the subscript records sites. GrowthTransfer.result consumes this bridge for the exact d=1,r=2 probability theorem. General Conjecture 3 remains outside this scope."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Telescope(Formula body) => All("m", Call("Nat"), All("w", Call("Word", F.Id("m")),
        All("d", Call("Assignment", F.Id("m")), All("h", Call("Certificate", F.Id("w"), F.Id("d")), body))));
    private static Formula MatchingFormula() => Disp(Telescope(Call("HasType", Call("matching", F.Id("h")), Call("Matching", Call("Fin", Add(F.Id("m"), D(6)))))));
    private static Formula ProfileFormula() => Disp(Telescope(Call("HasType", Call("profile", F.Id("h")), Call("Profile", Add(F.Id("m"), D(1))))));
    private static Formula AcceptableFormula() => Disp(Telescope(Call("IsAcceptable", Call("ring", Add(F.Id("m"),D(1))), Call("matching", F.Id("h")))));
    private static Formula StableFormula() => Disp(Telescope(Call("IsStable", Call("ring", Add(F.Id("m"),D(1))), Call("rank", Call("profile", F.Id("h"))), Call("matching", F.Id("h")))));
    private static Formula CloseFormula() => Disp(All("m",Call("Nat"), All("w",Call("CertifiedWord",F.Id("m")), Call("HasType",Call("close",F.Id("w")),Call("SuccessfulProfile",Add(F.Id("m"),D(1)))))));
    private static Formula InjectiveFormula() => Disp(All("m",Call("Nat"),Call("Injective",Call("close",F.Id("m")))));
    private static Formula CountFormula() => Disp(All("m",Call("Nat"),new Formula.Relation(Call("count",F.Id("m")),FormulaRelationOperator.LessThanOrEqual,Call("card",Call("SuccessfulProfile",Add(F.Id("m"),D(1)))))));
}
