using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class JointRewardFiberObstructionDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete stopped rewards can prevent removal of A despite cellwise numerical dominance.",
        H("Joint reward-fiber obstruction"),
        Blocks(
            Describe.Lean(DescribeId.Create("joint-reward-feature"),
                DeclarationHandle.Create(Owner + "feature"), H("Original quadratic coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every L, word and coordinate in Unit plus singleton addresses plus ordered distinct pairs, feature is the constant one, the selected bit, or the product of the selected two bits. The coordinate carrier uses Schedule L as an index set; it does not replace the words or their first-zero classes."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("joint-reward-moments"),
                DeclarationHandle.Create(Owner + "moments"), H("Actual full-cube moments"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every L and arbitrary real measure mu on the raw Boolean cube, moments mu sums mu times feature in each constant, singleton and ordered pair coordinate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("joint-reward-momentcone"),
                DeclarationHandle.Create(Owner + "MomentCone"), H("Actual first-zero moment cone"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every L, first-zero address i and complete quadratic vector v, MomentCone i v means that one actual nonnegative real measure on the entire cube represents v and vanishes outside the original class FirstZero i. No relaxation to independent marginal data is made."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("joint-reward-classbaselinemass"),
                DeclarationHandle.Create(Owner + "classBaselineMass"), H("Baseline mass in each first-zero class"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every L, full score y and address i, classBaselineMass sums A+P over precisely the original class FirstZero i. Terminal T is separate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("joint-reward-coupledfeasible"),
                DeclarationHandle.Create(Owner + "CoupledFeasible"), H("The coupled common-P constraints"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every L, full score y and families x,p of complete quadratic vectors indexed by every first-zero class, CoupledFeasible requires p, x-p and moments(numerical y i)-p to lie in the corresponding actual MomentCone; x's constant coordinate equals classBaselineMass; and the sum of all x vectors plus T times the terminal feature equals moments(baseline y). The same p is used in both differences, and the last equation is one aggregate equation on the common cube."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("joint-reward-commonmassset"),
                DeclarationHandle.Create(Owner + "commonMassSet"), H("All feasible common masses"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every L and full score y, commonMassSet contains exactly the sums of constant coordinates of p over all x,p satisfying CoupledFeasible. It includes all actual feasible variables and retains a single shared P vector for each class."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("joint-reward-jointmaximum"),
                DeclarationHandle.Create(Owner + "jointMaximum"), H("The coupled optimum J"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every L and full score y, jointMaximum is the supremum of commonMassSet. The theorem below proves that this supremum is an attained greatest element equal to zero for the four-word family."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("joint-reward-coefficientfloor"),
                DeclarationHandle.Create(Owner + "coefficientFloor"), H("The original coefficient floor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every L and full score y, coefficientFloor is T plus the sum over every first-zero class of the maximum of its baseline mass and its numerical-label mass. It is K floor in Definition 213.7 and Theorem 213.8."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("joint-reward-fibermassset"),
                DeclarationHandle.Create(Owner + "fiberMassSet"), H("All actual fiber coefficient masses"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every L and full score y, fiberMassSet consists of coefficientMass z for all arbitrary nonnegative full scores z with the same beta as y and the same baseline and numerical mass on every output fiber of every original stopped Catalog function. The proved equivalence with SameFiber preserves exactly the original individual cell-label rewards. All raw words, first-zero classes and original individual rewards remain constrained."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("joint-reward-coefficientminimum"),
                DeclarationHandle.Create(Owner + "coefficientMinimum"), H("The fiber coefficient minimum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every L and full score y, coefficientMinimum is the infimum of fiberMassSet. The theorem below supplies a least element and an actual attaining score for this family, without assuming Theorem 213.8."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("joint-reward-proposition21310-costs"),
                DeclarationHandle.Create(Owner + "proposition21310_costs"), H("Complete N and O costs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every L, ordered zero-based addresses n<j<k<l, late address n.val>=2 and positive real t, let y be witnessScore. Its entire beta function is 2t at n and zero elsewhere, its original anchor is t, and both complete supports are 3t and both complete costs are 2t. For every original schedule, every N or O cell and every empty cell, numerical label n+1 dominates the zero-label reward. The proof uses the whole-function Catalog correspondence for the support and for native output-fiber numerical dominance, identifies the reference-head functional with the anchor formula, bounds every label choice in every complete table and exhibits the constant numerical-label table attaining 3t; it uses no restriction on competitor supports."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("joint-reward-proposition21310-cone-minimum"),
                DeclarationHandle.Create(Owner + "proposition21310_cone_minimum"), H("Attained joint and coefficient extrema"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every L, n<j<k<l and positive real t, let y be witnessScore. Zero is a greatest element of commonMassSet and jointMaximum is zero. For all actual feasible x,p, every vector p i is zero. The value 4t is a least element of fiberMassSet, coefficientMinimum is 4t, coefficientFloor is 3t and the floor is strictly smaller than the minimum. An explicit feasible choice takes x at class n to be the moments of the actual base point of mass t, all other x to be zero and the shared p to be zero in every class. The source score itself attains the coefficient minimum. The cone proof chooses one P measure, one A residual and one C residual for each class, assembles the aggregate baseline, and applies the same nonnegative quadratic support separation. Direct polynomial formulas recover actual stopped readings from the complete moment vector; no general attainment or independent-P reconstruction theorem is assumed."))), DescribeRole.Theorem))));
}
