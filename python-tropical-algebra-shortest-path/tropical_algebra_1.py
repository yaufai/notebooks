from typing import List

# Definition of Infinity
inf = float("inf")

class TropicalVector:
    def __init__(self, vector: List[float]) -> None:
        self.vector = vector
    
    def __len__(self) -> int:
        return len(self.vector)
    
    def __getitem__(self, key: int) -> float:
        return self.vector[key]
    
    def __add__(self, vector: "TropicalVector") -> "TropicalVector":
        if len(self) == len(vector):
            return TropicalVector(
                [ min(self[i], vector[i]) for i in range(len(self)) ]
            )
        else:
            raise ValueError()
    
    # Inner product
    def __mul__(self, vector: "TropicalVector") -> float:
        if len(self) == len(vector):
            return min(
                [ self[i] + vector[i] for i in range(len(self)) ]
            )
        else:
            raise ValueError()
    
    def __str__(self) -> str:
        return str(self.vector)
    
class TropicalAdjacencyMatrix:
    def __init__(self, matrix: List[TropicalVector]) -> None:
        self.matrix = matrix
    
    def __add__(self, adjacency: "TropicalAdjacencyMatrix") -> "TropicalAdjacencyMatrix":
        if len(self.matrix) == len(adjacency.matrix):
            return TropicalAdjacencyMatrix(
                [ self.matrix[i] + adjacency.matrix[i]
                for i in range(len(self.matrix)) ]
            )
        else:
            raise ValueError()
    
    def __mul__(self, adjacency: "TropicalAdjacencyMatrix") -> "TropicalAdjacencyMatrix":
        def compute_line(line_idx: int) -> TropicalVector:
            line = self.matrix[line_idx]
            return TropicalVector([
                line * adjacency.transpose().matrix[i]
                for i in range(len(line))
            ])
        return TropicalAdjacencyMatrix([
            compute_line(line_idx) 
            for line_idx in range(len(self.matrix))
        ])
    
    def __pow__(self, power: int) -> "TropicalAdjacencyMatrix":
        if power < 1:
            # The identity matrix nor inverses are not defined. Therefore, nonpositive power is not given. 
            raise NotImplementedError()
        elif power == 1:
            return self
        else:
            return self * (self ** (power - 1))
    
    def __str__(self) -> str:
        return str(
            list(map(lambda vec: str(vec), self.matrix))
        )
    
    def transpose(self) -> "TropicalAdjacencyMatrix":
        def compute_line(line_idx: int) -> TropicalVector:
            return TropicalVector([
                self.matrix[i][line_idx]
                for i in range(len(self.matrix))
            ])
        return TropicalAdjacencyMatrix(
            [ compute_line(line_idx)
            for line_idx in range(len(self.matrix[0]))]
        )

A = TropicalAdjacencyMatrix([
    TropicalVector([ inf,   2,   4, inf ]),
    TropicalVector([ inf,   0,   1,   9 ]),
    TropicalVector([ inf, inf, inf,   5 ]),
    TropicalVector([   3, inf, inf, inf ])
])

if __name__ == "__main__":
    print(A ** 2)
    print(A ** 3)