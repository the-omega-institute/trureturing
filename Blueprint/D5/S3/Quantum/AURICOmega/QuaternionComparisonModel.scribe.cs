using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class QuaternionComparisonModelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/QuaternionComparisonModel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The unit quaternions with the half-shifted inner product form a ternary comparison structure that is order sensitive, touches zero, is chain connected and has feature rank five.",
        H("The unit quaternion comparison model"),
        Blocks(
            Node("inner-components", "inner_eq_components", "The quaternion inner product in components",
                StatementSource.FromAuthor(InnerComponentsFormula()), DescribeRole.Lemma,
                "The real inner product of two quaternions is the real part of star p * q. "
                    + "Since star p has components re p, -imI p, -imJ p and -imK p, that real part is the sum of the four products of corresponding components."),
            Node("model", "quaternionModel", "The unit quaternions as a ternary comparison structure",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "The carrier is the group of unit quaternions, the unitary elements of the real quaternion algebra. "
                    + "The transfer is tri x y z = x * y^-1 * z and the reading is kappa x y = (1 + <x, y>) / 2, where <p, q> = re p * re q + imI p * imI q + imJ p * imJ q + imK p * imK q is the real inner product of the quaternion algebra. "
                    + "The transfer identities are group identities. The reading is symmetric; it equals one exactly when x = y, because two unit vectors have inner product one only when they coincide; it is nonnegative because the inner product of two unit vectors is at least -1. "
                    + "Left and right multiplication by a unit quaternion preserve the inner product, which gives the two invariance laws of the reading under transfer. "
                    + "The Gram forms are nonnegative because the reading is the inner product of the feature vectors described below, so each Gram form is the squared norm of a combination of feature vectors."),
            Node("unit-i", "unitI", "The unit quaternion i",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "unitI is the quaternion with real part 0 and imaginary components imI = 1, imJ = 0, imK = 0, regarded as a unit quaternion: "
                    + "star i * i = 1 and i * star i = 1."),
            Node("noncommutative", "quaternionModel_noncommutative", "The model is order sensitive",
                StatementSource.FromAuthor(Disp(Call("Noncommutative", Model))), DescribeRole.Theorem,
                "Take the unit quaternions i, 1 and j. Then tri i 1 j = i * j = k while tri j 1 i = j * i = -k; their k-components are 1 and -1, so the two transfers differ."),
            Node("touches-zero", "quaternionModel_touchesZero", "The reading touches zero",
                StatementSource.FromAuthor(Disp(Call("TouchesZero", Model))), DescribeRole.Theorem,
                "The antipodal pair 1 and -1 has <1, -1> = -1, so its reading is (1 - 1) / 2 = 0, which is below every positive real e."),
            Node("chain-connected", "quaternionModel_chainConnected", "The model is chain connected",
                StatementSource.FromAuthor(Disp(Call("ChainConnected", Model))), DescribeRole.Theorem,
                "The unit quaternions are exactly the quaternions of norm one, the unit three-sphere in a real space of dimension four, and this sphere is connected. "
                    + "For a fixed point a the reading kappa a b is continuous in b and equals one at b = a, so for positive e every b near a satisfies 1 - e < kappa a b and, by symmetry, 1 - e < kappa b a. "
                    + "Thus, for each point a, the relation holds in both directions, from a to b and from b to a, for every b in a neighbourhood of a. On a connected space, a transitive relation with this two-sided neighbourhood property holds between all pairs; applied to the reflexive transitive closure of 1 - e < kappa a b, this joins any two unit quaternions."),
            Node("feature-rank-five", "quaternionModel_hasFeatureRank_five", "The reading has feature rank five",
                StatementSource.FromAuthor(Disp(Call("HasFeatureRank", Model, D(5)))), DescribeRole.Theorem,
                "The feature map sends q to (1 / sqrt 2) * (1, re q, imI q, imJ q, imK q) in Euclidean five-space. "
                    + "The inner product of the features of p and q is (1 / 2) * (1 + <p, q>), which is the reading of p and q."))));

    private static Formula Model => Seq(Operatorname, Grp(F.Id("quaternionModel")));

    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);

    private static Formula InnerComponentsFormula()
    {
        Formula p = F.Id("p"), q = F.Id("q");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula quaternions = Seq(Mathbb, Grp(F.Id("H")), OpenBracket, reals, CloseBracket);
        Formula inner = new Formula.Subscript(Seq(Langle, Sp, p, Comma, Sp, q, Sp, Rangle), reals);
        Formula term(string part) => Mul(Call(part, p), Call(part, q));
        Formula sum = Add(Add(Add(term("re"), term("imI")), term("imJ")), term("imK"));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("p"), quaternions),
             new Formula.BoundVariable(FormulaIdentifier.Create("q"), quaternions)],
            new Formula.Relation(inner, FormulaRelationOperator.Equal, sum)));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("quaternion-comparison-model-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
