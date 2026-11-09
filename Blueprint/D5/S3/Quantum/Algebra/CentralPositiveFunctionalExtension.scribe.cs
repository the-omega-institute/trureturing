using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class CentralPositiveFunctionalExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive ambient extensions represent every bounded real functional on a self-adjoint real subspace with exact total mass.",
        H("Norm-additive positive ambient extensions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-positive-extensions-norm-additive"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/CentralPositiveFunctionalExtension.exists_positive_extensions_norm_additive"),
                H("Positive extensions with total mass equal to the operator norm"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let A have exactly the classes CStarAlgebra A, PartialOrder A and StarOrderedRing A. "
                        + "Let X be any real Submodule of A, let hX assert that every element of X is self-adjoint, "
                        + "and let phi be any StrongDual real X, with its inherited norm and topology. "
                        + "There exist positive continuous complex-linear maps psiPlus and psiMinus from A to Complex "
                        + "whose real difference agrees with phi on every x in X and whose real values at the unit sum to the operator norm of phi.")),
                    Paragraph(Text(
                        "X need not contain the unit, be closed, or be complete. The zero subspace, zero functional, "
                        + "subsingleton ambient algebra and zero total mass are included, without a nontriviality or normalization hypothesis. "
                        + "In the display, val is the inclusion of X in A, one(A) is the ambient unit, "
                        + "re is the real part, and norm(phi) is the continuous real functional's operator norm.")),
                    Paragraph(Text(
                        "For a nontrivial ambient algebra the self-adjoint spectral estimate gives "
                        + "the exact product norm of (x+t1,-x+t1) as norm(x)+abs(t). "
                        + "On its actual linear range in A x A, the functional phi(x)+norm(phi)t is bounded by norm(phi). "
                        + "Mathlib's exists_extension_norm_eq supplies a real Hahn-Banach extension G. "
                        + "StrongDual.extendRCLike preserves its norm and real part; equality of norm and unit value "
                        + "then supplies positivity through ContinuousLinearMap.monotone_iff_opNorm_eq_map_one. "
                        + "Restriction to the two product coordinates gives the same pair satisfying both conclusion clauses.")),
                    Paragraph(Text(
                        "This is a repository-derived composition of the cited spectral and extension interfaces, with no novelty claim. "
                        + "It supplies analytic machinery for the central-response problem. "
                        + "The full signed overlap budget of 95.1 and identification of the original coset slope with the kernel response in 96.1 "
                        + "remain separate mathematical obligations; this theorem asserts neither conclusion."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var A = F.Id("A");
        var X = F.Id("X");
        var x = F.Id("x");
        var phi = F.Id("phi");
        var plus = F.Id("psiPlus");
        var minus = F.Id("psiMinus");
        var real = Call("Real");
        var complex = Call("Complex");
        var positiveMap = Call("PositiveContinuousLinearMap", complex, A, complex);
        var agreement = All("x", X, Equal(Apply(phi, x),
            Subtract(Call("re", Apply(plus, Call("val", x))),
                Call("re", Apply(minus, Call("val", x))))));
        var mass = Equal(
            new Formula.Binary(Call("re", Apply(plus, Call("one", A))),
                FormulaBinaryOperator.Add, Call("re", Apply(minus, Call("one", A)))),
            Call("norm", phi));
        var result = Exists("psiPlus", positiveMap,
            Exists("psiMinus", positiveMap,
                new Formula.Logic(agreement, FormulaLogicOperator.And, mass)));
        var selfadjoint = All("x", X, Call("IsSelfAdjoint", Call("val", x)));
        return All("A", Seq(Call("Type"), Star),
            Instance(Call("CStarAlgebra", A),
            Instance(Call("PartialOrder", A),
            Instance(Call("StarOrderedRing", A),
                All("X", Call("Submodule", real, A),
                    new Formula.Logic(selfadjoint, FormulaLogicOperator.Implies,
                        All("phi", Call("StrongDual", real, X), result)))))));
    }

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
