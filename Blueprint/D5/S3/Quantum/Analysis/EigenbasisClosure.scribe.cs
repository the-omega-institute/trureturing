using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class EigenbasisClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real eigenvalues on a complete orthonormal family determine a self-adjoint closure.",
        H("Real Eigenbasis Closure"),
        Blocks(Describe.Lean(
            DescribeId.Create("real-eigenbasis-closure"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/EigenbasisClosure.eigenbasis_closable_selfAdjoint"),
            H("The finite eigenbasis operator has a genuine self-adjoint closure"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Analytic/diem2026eigenbasisclosure")),
            Blocks(
                Paragraph(Text("Let H be a complete complex inner product space and let e be "
                    + "a Hilbert basis indexed by any type I. Let T have exactly the algebraic "
                    + "span of those vectors as its domain. If each vector e of i is an "
                    + "eigenvector with real eigenvalue lambda of i, then T is closable "
                    + "and its genuine closure is self-adjoint.")),
                Paragraph(Text("The coefficients c of i divided by lambda of i minus zeta "
                    + "are square summable when zeta is plus or minus i. The denominator "
                    + "has modulus at least one. Common finite sums converge in both graph "
                    + "coordinates, and the two surjective resolvents identify the closure "
                    + "with its adjoint. Zero and repeated eigenvalues are allowed."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula h = F.Id("H"), i = F.Id("I"), e = F.Id("e"), t = F.Id("T"), l = F.Id("lambda");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula vector = new Formula.Apply(e, [F.Id("j")]);
        Formula eigen = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("j"), i)], Equal(new Formula.Apply(t, [vector]),
                new Formula.Binary(new Formula.Apply(l, [F.Id("j")]), FormulaBinaryOperator.Multiply, vector)));
        Formula domain = Equal(Call("domain", t), Call("span", Call("range", e)));
        Formula assumptions = new Formula.Logic(domain, FormulaLogicOperator.And, eigen);
        Formula conclusion = new Formula.Logic(Call("Closable", t), FormulaLogicOperator.And,
            Call("SelfAdjoint", Call("closure", t)));
        return new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("H"), F.Id("CompleteComplexInnerProductSpace")),
             new(FormulaIdentifier.Create("I"), F.Id("Type")),
             new(FormulaIdentifier.Create("e"), Call("HilbertBasis", i, h)),
             new(FormulaIdentifier.Create("T"), Call("LinearPartialOperator", h)),
             new(FormulaIdentifier.Create("lambda"), new Formula.TypeArrow(i, real))],
            new Formula.Logic(assumptions, FormulaLogicOperator.Implies, conclusion));
    }
}
