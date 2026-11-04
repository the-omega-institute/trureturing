using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class LorentzGramDeterminantDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Hyperideal/LorentzGramDeterminant.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lorentz Gram determinants are negative squares of realizing determinants.",
        H("The determinant of a Lorentz Gram matrix"),
        Blocks(
            Paragraph(Text("A four by four real matrix M has row vectors in the standard "
                + "space-positive, time-negative Lorentz form. If G is their pairwise Gram "
                + "matrix, then G=M J M^T for J=diag(1,1,1,-1). The determinant therefore "
                + "records the orientation-free volume square with the single Lorentz sign.")),
            Describe.Lean(
                DescribeId.Create("lorentz-gram-determinant"),
                DeclarationHandle.Create(Prefix + "lorentz_gram_determinant"),
                H("Exact Lorentz Gram determinant identity"),
                StatementSource.FromAuthor(F.Disp(LorentzGramStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The proof first identifies the Gram matrix with the "
                    + "explicit matrix product M*J*M-transpose by expanding the finite Lorentz "
                    + "sum. Multiplicativity of determinant, transpose invariance, and the "
                    + "four diagonal entries of J then give det(G)=-(det(M))^2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("length-gram-determinant-factorization"),
                DeclarationHandle.Create(Prefix + "length_gram_determinant_factorization"),
                H("The six-length Gram specialization"),
                StatementSource.FromAuthor(F.Disp(LengthGramStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Applying the general identity to the existing LengthGramBody "
                    + "lengthGram matrix gives the determinant factorization for every supplied "
                    + "Lorentz realization of the same six-length Gram data."))),
                DescribeRole.Theorem)
        )));

    private static Formula LorentzGramStatement()
    {
        var M = F.Id("M"); var G = F.Id("G");
        var i = F.Id("i"); var j = F.Id("j");
        var equality = Eq(Call("lorentz", Call("row", M, i), Call("row", M, j)),
            Call("entry", G, i, j));
        var hypothesis = All("i", F.Id("Fin4"), All("j", F.Id("Fin4"), equality));
        return All("M", F.Id("Mat4"), All("G", F.Id("Mat4"),
            Impl(hypothesis, Eq(Call("det", G), Neg(Pow(Call("det", M), F.D(2)))))));
    }

    private static Formula LengthGramStatement()
    {
        var l = F.Id("l"); var M = F.Id("M");
        var i = F.Id("i"); var j = F.Id("j");
        var equality = Eq(Call("lorentz", Call("row", M, i), Call("row", M, j)),
            Call("lengthGram", l, i, j));
        var hypothesis = All("i", F.Id("Fin4"), All("j", F.Id("Fin4"), equality));
        return All("l", F.Id("Length6"), All("M", F.Id("Mat4"),
            Impl(hypothesis, Eq(Call("det", Call("lengthGram", l)),
                Neg(Pow(Call("det", M), F.D(2)))))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Impl(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Neg(Formula x) => new Formula.Negate(x);
    private static Formula Pow(Formula x, Formula n) => new Formula.Power(x, n);
}

