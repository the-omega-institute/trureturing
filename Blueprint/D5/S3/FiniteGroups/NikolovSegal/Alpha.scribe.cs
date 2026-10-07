using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class AlphaDocument : IScribeDocumentDefinition
{

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("The alternating section degrees of a finite group form a nonempty bounded set whose supremum is attained.",
        H("The Largest Alternating Section Degree"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-alpha-alternatingdegrees"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Alpha.alternatingDegrees"),
                H("The set of alternating degrees"),
                StatementSource.FromAuthor(Disp(Groups("G",All("k",Nat,Iff(C("Member",k,C("alternatingDegrees",G)),I(Alt(k),G)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The set alternatingDegrees(G) consists exactly of natural numbers k for which Alt(k) is a section of G. It includes the trivial alternating groups at small degrees."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-alpha-alpha"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Alpha.alpha"),
                H("The alternating section invariant"),
                StatementSource.FromAuthor(Disp(Groups("G",Eq(C("alpha",G),C("sSup",C("alternatingDegrees",G)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The invariant alpha(G) is the natural-number supremum of alternatingDegrees(G). The supremum uses the conditional supremum operation on natural numbers. For finite G, the results below establish boundedness and show that this is an attained largest degree."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-alpha-alternatingdegrees-nonempty"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Alpha.alternatingDegrees_nonempty"),
                H("Degree zero supplies a section"),
                StatementSource.FromAuthor(Disp(Groups("G",C("Nonempty",C("alternatingDegrees",G))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The alternating group on Fin(0) is trivial, so the trivial homomorphism from G onto it is surjective. No finiteness hypothesis is needed for nonemptiness."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-alpha-alternating-degree-card-bound"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Alpha.alternating_degree_card_bound"),
                H("A cardinal bound for every section degree"),
                StatementSource.FromAuthor(Disp(Groups("G",Imp(C("Finite",G),All("k",Nat,Imp(I(Alt(k),G),Le(k,C("add",C("mul",new Formula.Number(2),C("card",G)),new Formula.Number(1))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For degree at least two, twice the alternating order is k factorial. Section-order divisibility bounds that order by the finite ambient order, and k is at most k factorial. Degrees zero and one satisfy the displayed bound directly."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-alpha-alternatingdegrees-bddabove"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Alpha.alternatingDegrees_bddAbove"),
                H("Finite groups have bounded section degrees"),
                StatementSource.FromAuthor(Disp(Groups("G",Imp(C("Finite",G),C("BddAbove",C("alternatingDegrees",G)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every alternating section degree is at most twice the ambient order plus one. Thus the natural-number supremum has a finite upper bound."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-alpha-alpha-spec"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Alpha.alpha_spec"),
                H("The supremum is an attained maximum"),
                StatementSource.FromAuthor(Disp(Groups("G",Imp(C("Finite",G),And(I(Alt(C("alpha",G)),G),All("k",Nat,Imp(I(Alt(k),G),Le(k,C("alpha",G))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite group, Alt(alpha(G)) is actually a section of G, and every alternating section degree is at most alpha(G). Nonemptiness and boundedness justify attainment; alpha is not merely an upper-bound surrogate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-alpha-alpha-le-max-of-section-transfer"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Alpha.alpha_le_max_of_section_transfer"),
                H("All large-degree transfers give the maximum bound"),
                StatementSource.FromAuthor(Disp(Groups("GQ",Imp(C("Finite",Q),Imp(All("k",Nat,Imp(And(Le(new Formula.Number(5),k),I(Alt(k),G)),I(Alt(k),Q))),Le(C("alpha",G),C("max",C("alpha",Q),new Formula.Number(4)))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The source group need not be finite in this implication. Every degree at most four is bounded by the second maximum argument; every larger section transfers to the finite target and is bounded by its attained alpha."))),
                DescribeRole.Lemma))));

    private static Formula G => F.Id("G");
    private static Formula Q => F.Id("Q");
    private static Formula k => F.Id("k");
    private static Formula Nat => F.Id("Nat");
    private static Formula C(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula I(Formula section, Formula group) => C("Involves", section, group);
    private static Formula Alt(Formula degree) => C("alternatingGroup", C("Fin", degree));
    private static Formula Eq(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.Equal, r);
    private static Formula Le(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.LessThanOrEqual, r);
    private static Formula Imp(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Implies, r);
    private static Formula Iff(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Iff, r);
    private static Formula And(Formula first, params Formula[] rest)
    {
        Formula result = first;
        foreach (Formula next in rest) result = new Formula.Logic(result, FormulaLogicOperator.And, next);
        return result;
    }
    private static Formula All(string name, Formula domain, Formula body) => new Formula.BindMany(
        FormulaQuantifier.ForAll, [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);
    private static Formula OneGroup(string name, string universe, Formula body) =>
        All(name, F.Id(universe), Imp(C("Group", F.Id(name)), body));
    private static Formula Groups(string names, Formula body) => names switch
    {
        "G" => OneGroup("G", "Typev", body),
        "AG" => OneGroup("A", "Typeu", OneGroup("G", "Typev", body)),
        "GQ" => OneGroup("G", "Typev", OneGroup("Q", "Typew", body)),
        "AGQ" => OneGroup("A", "Typeu", OneGroup("G", "Typev", OneGroup("Q", "Typew", body))),
        _ => body,
    };
}
