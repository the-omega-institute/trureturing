using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class SylowKernelDocument : IScribeDocumentDefinition
{

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("The normalizer of a Sylow p-subgroup excludes simple sections with p-divisible order that are not p-groups.",
        H("Simple Sections of Sylow Normalizers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-sylowkernel-not-involves-sylow-normalizer"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/SylowKernel.not_involves_sylow_normalizer"),
                H("The Sylow-normalizer obstruction"),
                StatementSource.FromAuthor(Disp(Groups("AG",Imp(And(C("Finite",G),C("Simple",A)),All("p",Nat,Imp(C("Prime",p),All("P",C("Sylow",p,G),Imp(And(Not(C("IsPGroup",p,A)),Dvd(p,C("card",A))),Not(I(A,C("normalizer",P))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Here P is a Sylow p-subgroup of finite G and normalizer(P) is its normalizer in G. Inside that normalizer, P is normal and is a p-group, while the quotient order is not divisible by p. A simple section must occur in the kernel or quotient. The p-group obstruction excludes the kernel branch; divisibility excludes the quotient branch."))),
                DescribeRole.Theorem))));

    private static Formula A => F.Id("A");
    private static Formula G => F.Id("G");
    private static Formula P => F.Id("P");
    private static Formula p => F.Id("p");
    private static Formula Nat => F.Id("Nat");
    private static Formula C(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula I(Formula section, Formula group) => C("Involves", section, group);
    private static Formula Dvd(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.Divides, r);
    private static Formula Imp(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Implies, r);
    private static Formula Not(Formula body) => new Formula.Not(body);
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
