#include <stdio.h>
#include <stdlib.h>
#include <time.h>

int main(int argc, char *argv[]){
    if (argc < 4){
        printf("Missing arg \n");
        printf("ARGS : NB_VARS NB_CLAUSES MAX_CLAUSE_LENGTH\n");
        return 1;
    }
    FILE* file = fopen("test.cnfuf", "w+");
    if(file == NULL){
        printf("Can't open file ! \n");
        return 1;
    }
    int nb_vars = atoi(argv[1]);
    int nb_clause = atoi(argv[2]);
    int max_clause_length = atoi(argv[3]);

    fprintf(file, "p cnf %d %d\n", nb_vars, nb_clause);
    for(int i = 0; i < nb_clause; i++){
        int l = 1 + (rand() % (max_clause_length - 1));
        for (int j = 0; j <l ; j++){
            int x = 1 + (rand() % (nb_vars - 1));
            int y = 1 + (rand() % (nb_vars - 1));
            int equal = rand() % 2;
            if(equal) fprintf(file, "%d=%d ", x, y);
            else fprintf(file, "%d<>%d ", x, y);
        }
        fprintf(file, "\n");
    }
    fclose(file);
    return 0;
}
