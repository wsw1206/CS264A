#include <stdio.h>
#include <stdlib.h>

#include "vector.h"

void vector_init(vector* v) {
	v->data = NULL;
	v->capacity = 0;
	v->size = 0;
}

c2dSize vector_size(const vector* v) {
	return v->size;
}

void vector_push(vector* v, void* e) {
	if (v->capacity == 0) {
		v->capacity = 2;
		v->data = malloc(sizeof(void*) * v->capacity);
	}
	if (v->capacity == v->size) {
		v->capacity *= 2;
		v->data = realloc(v->data, sizeof(void*) * v->capacity);
	}
	v->data[v->size++] = e;
}

void vector_pop(vector* v) {
	if (v->size > 0) {
		v->size--;
		if (v->size * 2 < v->capacity) {
			v->capacity /= 2;
			v->data = realloc(v->data, sizeof(void*) * v->capacity);
		}
	}
}

void* vector_get(const vector* v, c2dSize index) {
	return v->data[index];
}

void* vector_top(const vector*v) {
	return v->data[v->size - 1];
}

void vector_set(vector* v, c2dSize index, void* e) {
	v->data[index] = e;
}

void vector_erase(vector* v, c2dSize index) {
	if (index < v->size - 1)
		v->data[index] = v->data[v->size - 1];
	vector_pop(v);
}

void vector_free(vector* v) {
	free(v->data);
}

void** vector_toarr(const vector* v) {
	return v->data;
}
