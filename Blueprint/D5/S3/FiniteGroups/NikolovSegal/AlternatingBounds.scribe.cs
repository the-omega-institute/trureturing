using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class AlternatingBoundsDocument : IScribeDocumentDefinition
{

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Alternating groups of degree at least five have order divisible by sixty and cannot be 2-groups.",
        H("Orders of Large Alternating Groups"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-alternatingbounds-sixty-dvd-card-alternating"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/AlternatingBounds.sixty_dvd_card_alternating"),
                H("Sixty divides the alternating order"),
                StatementSource.FromAuthor(Disp(All("k",Nat,Imp(Le(new Formula.Number(5),k),Dvd(new Formula.Number(60),C("card",Alt(k))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Alt(k) denotes the alternating group on Fin(k). Twice its order equals k factorial. For k at least five, divisibility by 5 factorial gives divisibility of the order by sixty."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-alternatingbounds-two-dvd-card-alternating"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/AlternatingBounds.two_dvd_card_alternating"),
                H("Large alternating groups have even order"),
                StatementSource.FromAuthor(Disp(All("k",Nat,Imp(Le(new Formula.Number(5),k),Dvd(new Formula.Number(2),C("card",Alt(k))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the even-order consequence of divisibility by sixty, used when applying the Sylow 2-subgroup obstruction."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-alternatingbounds-alternating-not-twogroup"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/AlternatingBounds.alternating_not_twoGroup"),
                H("Large alternating groups are not 2-groups"),
                StatementSource.FromAuthor(Disp(All("k",Nat,Imp(Le(new Formula.Number(5),k),Not(C("IsPGroup",new Formula.Number(2),Alt(k))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite 2-group has order a power of two. Three divides sixty and hence the order of Alt(k) for k at least five, contradicting that power-of-two order."))),
                DescribeRole.Lemma))));

    private static Formula k => F.Id("k");
    private static Formula Nat => F.Id("Nat");
    private static Formula C(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Alt(Formula degree) => C("alternatingGroup", C("Fin", degree));
    private static Formula Le(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.LessThanOrEqual, r);
    private static Formula Dvd(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.Divides, r);
    private static Formula Imp(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Implies, r);
    private static Formula Not(Formula body) => new Formula.Not(body);
    private static Formula All(string name, Formula domain, Formula body) => new Formula.BindMany(
        FormulaQuantifier.ForAll, [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);
}
